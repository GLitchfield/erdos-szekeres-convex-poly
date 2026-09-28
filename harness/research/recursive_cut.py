"""Bounded two-marker cut probe using the retained recursive evaluator.

The probe promotes the deterministic family from the September 13
``extreme_next_probe.py`` run into the generic ``es probe`` interface.  Both
recursive semantics are implementation versions only: this module makes no
claim that either evaluator is equivalent to a Lean definition.
"""
from __future__ import annotations

from collections import Counter
import itertools
import math
import re
import signal
import time

from .primitives import part
from .recursive import VERSIONS, evaluator


DOMAIN = "two-lower-marker-cut-family-v1"
GENERATOR = "extreme-next-deterministic-v1"
CANDIDATE = "matched-coupling-budgets-v1"
SPLIT_RULE = "nonempty-proper-child-subsets-with-geometry-v1"
SAMPLE_CAP = 3
MAX_CACHE_SIZE = 1_000_000
MAX_PER_CASE_SECONDS = 60.0
_MEMORY = re.compile(r"^[1-9][0-9]*(?:K|M|G|T)$")


class CaseTimeout(Exception):
    """The retained evaluator exceeded this probe's per-case limit."""


def _expired(*_):
    raise CaseTimeout()


def _integer(value, name, *, low=None, high=None):
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer")
    if low is not None and value < low:
        raise ValueError(f"{name} must be at least {low}")
    if high is not None and value > high:
        raise ValueError(f"{name} must be at most {high}")
    return value


def _number(value, name, *, low=None, high=None):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{name} must be a number")
    value = float(value)
    if not math.isfinite(value):
        raise ValueError(f"{name} must be finite")
    if low is not None and value < low:
        raise ValueError(f"{name} must be at least {low}")
    if high is not None and value > high:
        raise ValueError(f"{name} must be at most {high}")
    return value


def _integer_list(value, name, *, low, high, minimum_length=1, unique=True):
    if not isinstance(value, list) or len(value) < minimum_length:
        raise ValueError(f"{name} must be a nonempty list")
    result = [_integer(item, f"{name} item", low=low, high=high) for item in value]
    if unique and len(result) != len(set(result)):
        raise ValueError(f"{name} must not contain duplicates")
    return tuple(result)


def _candidate(spec, k):
    candidate = spec.get("candidate")
    if not isinstance(candidate, dict) or candidate.get("name") != CANDIDATE:
        raise ValueError(f"candidate.name must be {CANDIDATE}")
    normalized = {"name": CANDIDATE}
    for label in ("target", "control"):
        value = candidate.get(label)
        if not isinstance(value, dict):
            raise ValueError(f"candidate.{label} must be an object")
        m = _integer(value.get("m"), f"candidate.{label}.m", low=1, high=k - 2)
        n = _integer(value.get("n"), f"candidate.{label}.n", low=1, high=k - 2)
        if m + n != k - 1:
            raise ValueError(f"candidate.{label} must satisfy m+n=k-1")
        normalized[label] = {"m": m, "n": n}
    normalized["target"]["budget"] = _integer(
        candidate["target"].get("budget"), "candidate.target.budget", low=0)
    normalized["control"]["top_budget"] = _integer(
        candidate["control"].get("top_budget"), "candidate.control.top_budget", low=0)
    normalized["control"]["next_budget"] = _integer(
        candidate["control"].get("next_budget"), "candidate.control.next_budget", low=0)
    if normalized["control"]["next_budget"] > normalized["control"]["top_budget"]:
        raise ValueError("candidate.control.next_budget must not exceed top_budget")
    return normalized


def _validated_spec(spec):
    if not isinstance(spec, dict) or spec.get("schema_version") != 1:
        raise ValueError("schema_version must be 1")
    if spec.get("plugin") != "recursive_cut":
        raise ValueError("plugin must be recursive_cut")
    semantics = spec.get("semantics")
    if semantics not in VERSIONS:
        raise ValueError("explicit registered recursion semantics required")
    if spec.get("domain") != DOMAIN:
        raise ValueError(f"domain must be {DOMAIN}")
    if spec.get("stop") != "first_witness":
        raise ValueError("stop must be first_witness")

    generator = spec.get("generator")
    if not isinstance(generator, dict) or generator.get("name") != GENERATOR:
        raise ValueError(f"generator.name must be {GENERATOR}")
    if generator.get("split_rule") != SPLIT_RULE:
        raise ValueError(f"generator.split_rule must be {SPLIT_RULE}")
    source = generator.get("source")
    if not isinstance(source, dict):
        raise ValueError("generator.source must be an object")
    a = _integer(source.get("a"), "generator.source.a", low=2, high=20)
    u = _integer(source.get("u"), "generator.source.u", low=2, high=20)
    k = _integer(source.get("k"), "generator.source.k", low=3, high=20)
    if a > k or u > k:
        raise ValueError("generator source must satisfy a<=k and u<=k")
    if source.get("chosen_side") != "lower" or source.get("marker_side") != "lower":
        raise ValueError("this family requires lower chosen and marker sides")
    if source.get("marker_levels") != [1, 2]:
        raise ValueError("this family requires marker_levels [1, 2]")
    child_counts = _integer_list(
        generator.get("child_counts"), "generator.child_counts", low=2, high=8)
    maxima_values = _integer_list(
        generator.get("maxima_values"), "generator.maxima_values", low=0, high=k - 2)
    if not any(value > 0 for value in maxima_values):
        raise ValueError("generator.maxima_values requires a positive value")
    orders = generator.get("marker_orders")
    if not isinstance(orders, list) or not orders:
        raise ValueError("generator.marker_orders must be a nonempty list")
    marker_orders = []
    for order in orders:
        if not isinstance(order, list) or sorted(order) != [1, 2]:
            raise ValueError("each marker order must be a permutation of [1, 2]")
        marker_orders.append(tuple(order))
    if len(marker_orders) != len(set(marker_orders)):
        raise ValueError("generator.marker_orders must not contain duplicates")

    budget = spec.get("budget")
    if not isinstance(budget, dict):
        raise ValueError("budget must be an object")
    cases = _integer(budget.get("cases"), "budget.cases", low=1)
    seconds = _number(budget.get("seconds"), "budget.seconds", low=0.001, high=86_400)
    memory = budget.get("memory")
    if not isinstance(memory, str) or not _MEMORY.fullmatch(memory):
        raise ValueError("budget.memory must be a positive K/M/G/T size")

    settings = spec.get("evaluator")
    if not isinstance(settings, dict):
        raise ValueError("evaluator must be an object")
    cache_size = _integer(
        settings.get("cache_size"), "evaluator.cache_size", low=1, high=MAX_CACHE_SIZE)
    per_case_seconds = _number(
        settings.get("per_case_seconds"), "evaluator.per_case_seconds",
        low=0.001, high=MAX_PER_CASE_SECONDS)
    if per_case_seconds > seconds:
        raise ValueError("evaluator.per_case_seconds must not exceed budget.seconds")

    return {
        "semantics": semantics,
        "source": {"a": a, "u": u, "k": k, "chosen": "lower"},
        "child_counts": child_counts,
        "maxima_values": maxima_values,
        "marker_orders": tuple(marker_orders),
        "candidate": _candidate(spec, k),
        "budget": {"cases": cases, "seconds": seconds, "memory": memory},
        "evaluator": {"cache_size": cache_size, "per_case_seconds": per_case_seconds},
    }


def _compositions(total):
    for left in range(total + 1):
        for middle in range(total - left + 1):
            yield left, middle, total - left - middle


def _make_word(counts, order):
    word = []
    for index, count in enumerate(counts):
        word.extend(["S"] * count)
        if index < 2:
            word.append((order[index], "lower"))
    return tuple(word)


def _maxima_order(values):
    positive = list(itertools.product((value for value in values if value > 0), repeat=2))
    positive.sort(key=lambda pair: (sum(pair), pair))
    with_zero = [pair for pair in itertools.product(values, repeat=2) if 0 in pair]
    with_zero.sort(key=lambda pair: (-sum(pair), pair))
    return positive + with_zero


def _candidate_cases(config):
    words = []
    for children in config["child_counts"]:
        for order in config["marker_orders"]:
            for counts in _compositions(children):
                word = _make_word(counts, order)
                runs = sum(count > 0 for count in counts)
                words.append((children, runs, counts, order, word))
    words.sort(key=lambda item: (-item[0], -item[1], item[2], item[3]))
    for maxima in _maxima_order(config["maxima_values"]):
        for children, runs, counts, order, word in words:
            child_positions = tuple(i for i, token in enumerate(word) if token == "S")
            x = next(i for i, token in enumerate(word) if token != "S" and token[0] == 1)
            y = next(i for i, token in enumerate(word) if token != "S" and token[0] == 2)
            subsets = []
            for size in range(1, children):
                subsets.extend(itertools.combinations(child_positions, size))
            subsets.sort(key=lambda keep: (abs(2 * len(keep) - children), len(keep), keep))
            for keep in subsets:
                removed = tuple(position for position in child_positions if position not in keep)
                eligible = tuple(q for q in removed
                                 if (q < x and y < x) or (x < q and x < y))
                if eligible:
                    yield {
                        "children": children,
                        "runs": runs,
                        "counts": counts,
                        "marker_order": order,
                        "word": word,
                        "maxima": maxima,
                        "child_positions": child_positions,
                        "x": x,
                        "y": y,
                        "keep": keep,
                        "removed": removed,
                        "p": keep[0],
                        "q": eligible[0],
                    }


def _json_word(word):
    return [token if token == "S" else [token[0], token[1]] for token in word]


def _word(value):
    if not isinstance(value, list) or not value:
        raise ValueError("source.word must be a nonempty list")
    word = []
    for token in value:
        if token == "S":
            word.append("S")
        elif (isinstance(token, list) and len(token) == 2
              and type(token[0]) is int and token[0] in (1, 2)
              and token[1] == "lower"):
            word.append((token[0], token[1]))
        else:
            raise ValueError("source.word contains an invalid family token")
    return tuple(word)


def _signature(row):
    return {"word": _json_word(row["word"]), "maxima": list(row["maxima"])}


def _well_formed(source):
    levels = {}
    external_labels_in_range = True
    one_side_per_level = True
    for token in source["word"]:
        if token == "S":
            continue
        level, side = token
        external_labels_in_range &= 1 <= level <= len(source["maxima"])
        one_side_per_level &= levels.setdefault(level, side) == side
    conditions = {
        "global_bounds": 2 <= source["a"] <= source["k"] and 2 <= source["u"] <= source["k"],
        "positive_maxima_in_1_to_k_minus_2": all(
            1 <= value <= source["k"] - 2 for value in source["maxima"]),
        "external_labels_in_range": external_labels_in_range,
        "one_side_per_level": one_side_per_level,
    }
    conditions["all"] = all(conditions.values())
    return conditions


def _evaluate_pair(rec, source, keep, removed, m, n):
    left = part(source, keep, "lower", m)
    right = part(source, removed, "upper", n)
    return left, right, int(rec(left["word"], left["maxima"])), int(rec(right["word"], right["maxima"]))


def _evaluate_case(rec, config, case, case_index):
    source = config["source"] | {"word": case["word"], "maxima": case["maxima"]}
    target = config["candidate"]["target"]
    control = config["candidate"]["control"]
    control_a, control_b, control_av, control_bv = _evaluate_pair(
        rec, source, case["keep"], case["removed"], control["m"], control["n"])
    target_a, target_b, target_av, target_bv = _evaluate_pair(
        rec, source, case["keep"], case["removed"], target["m"], target["n"])
    control_sum = control_av + control_bv
    target_sum = target_av + target_bv
    row = {
        "case_index": case_index,
        "source": {
            "a": source["a"], "u": source["u"], "k": source["k"],
            "chosen": source["chosen"], "word": _json_word(source["word"]),
            "maxima": list(source["maxima"]),
            "well_formed_conditions": _well_formed(source),
        },
        "layout": {
            "children": case["children"], "child_runs": case["runs"],
            "run_counts": list(case["counts"]), "marker_order": list(case["marker_order"]),
            "child_positions": list(case["child_positions"]), "N": 1, "M": 2,
            "x": case["x"], "y": case["y"], "keep": list(case["keep"]),
            "removed": list(case["removed"]), "p": case["p"], "q": case["q"],
            "geometry_branch": "q<x and y<x" if case["q"] < case["x"] else "x<q and x<y",
        },
        "control": {
            "m": control["m"], "n": control["n"],
            "A": _signature(control_a), "B": _signature(control_b),
            "A_bound": control_av, "B_bound": control_bv, "sum": control_sum,
            "top_budget": control["top_budget"], "next_budget": control["next_budget"],
            "passes_top": control_sum <= control["top_budget"],
            "passes_next": control_sum <= control["next_budget"],
        },
        "target": {
            "m": target["m"], "n": target["n"],
            "A": _signature(target_a), "B": _signature(target_b),
            "A_bound": target_av, "B_bound": target_bv, "sum": target_sum,
            "budget": target["budget"], "excess": target_sum - target["budget"],
            "violates_budget": target_sum > target["budget"],
        },
    }
    return row


def _witness(row, config):
    return {
        "schema_version": 1,
        "semantics": config["semantics"],
        "domain": DOMAIN,
        "generator": GENERATOR,
        "split_rule": SPLIT_RULE,
        "source": row["source"],
        "layout": row["layout"],
        "candidate": config["candidate"],
        "evaluator": config["evaluator"],
    }


def _counter_dict(counter):
    return dict(sorted(counter.items(), key=lambda item: str(item[0])))


def evaluate(spec):
    """Evaluate a deterministic prefix of the declared finite cut family."""
    config = _validated_spec(spec)
    started = time.monotonic()
    budget = config["budget"]
    rec = evaluator(config["source"]["a"], config["source"]["u"], config["source"]["k"],
                    semantics=config["semantics"], cache_size=config["evaluator"]["cache_size"])
    counters = {
        "source_maxima": Counter(), "children": Counter(), "child_runs": Counter(),
        "geometry_branches": Counter(), "target_sums": Counter(), "control_sums": Counter(),
    }
    unique_words = set()
    admitted = completed = timeouts = generated = control_failures = 0
    rows = []
    found = None
    stop_reason = None
    iterator = iter(_candidate_cases(config))
    previous_handler = signal.getsignal(signal.SIGALRM)
    signal.signal(signal.SIGALRM, _expired)
    try:
        while True:
            try:
                case = next(iterator)
                generated += 1
            except StopIteration:
                stop_reason = "eligible_domain_exhausted"
                break
            elapsed = time.monotonic() - started
            if elapsed >= budget["seconds"]:
                stop_reason = "time_limit"
                break
            if admitted >= budget["cases"]:
                stop_reason = "case_limit"
                break
            admitted += 1
            remaining = budget["seconds"] - elapsed
            signal.setitimer(signal.ITIMER_REAL, min(config["evaluator"]["per_case_seconds"], remaining))
            try:
                row = _evaluate_case(rec, config, case, generated - 1)
            except CaseTimeout:
                timeouts += 1
                rec.cache_clear()
                continue
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            completed += 1
            if len(rows) < SAMPLE_CAP:
                rows.append(row)
            maxima_key = "[" + ", ".join(str(value) for value in case["maxima"]) + "]"
            counters["source_maxima"][maxima_key] += 1
            counters["children"][str(case["children"])] += 1
            counters["child_runs"][str(case["runs"])] += 1
            counters["geometry_branches"][row["layout"]["geometry_branch"]] += 1
            counters["target_sums"][str(row["target"]["sum"])] += 1
            counters["control_sums"][str(row["control"]["sum"])] += 1
            unique_words.add(tuple(case["word"]))
            control_failures += int(not row["control"]["passes_top"] or not row["control"]["passes_next"])
            if row["target"]["violates_budget"] and row["control"]["passes_next"]:
                found = _witness(row, config)
                stop_reason = "candidate_witness"
                break
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)

    exhaustive = stop_reason == "eligible_domain_exhausted" and timeouts == 0
    if found is not None:
        outcome = "witness_found"
    elif timeouts:
        outcome = "timeout"
    elif exhaustive:
        outcome = "exhaustive_on_declared_finite_domain"
    else:
        outcome = "no_witness_within_budget"
    cache = rec.cache_info()
    return {
        "schema_version": 1,
        "outcome": outcome,
        "witness": found,
        "stop_reason": stop_reason,
        "semantics": config["semantics"],
        "domain": DOMAIN,
        "generator": {
            "name": GENERATOR, "split_rule": SPLIT_RULE,
            "source": config["source"], "child_counts": list(config["child_counts"]),
            "maxima_values": list(config["maxima_values"]),
            "marker_orders": [list(order) for order in config["marker_orders"]],
        },
        "candidate": config["candidate"],
        "limits": config["budget"] | config["evaluator"],
        "coverage": {
            "generated": generated, "admitted": admitted, "completed": completed,
            "timeouts": timeouts, "control_failures": control_failures,
            "exhaustive": exhaustive, "source_maxima": _counter_dict(counters["source_maxima"]),
            "children": _counter_dict(counters["children"]),
            "child_runs": _counter_dict(counters["child_runs"]),
            "geometry_branches": _counter_dict(counters["geometry_branches"]),
            "unique_source_words": len(unique_words),
            "target_sums": _counter_dict(counters["target_sums"]),
            "control_sums": _counter_dict(counters["control_sums"]),
        },
        "sample_rows": rows,
        "seconds": time.monotonic() - started,
        "cache": {"hits": cache.hits, "misses": cache.misses,
                  "maxsize": cache.maxsize, "currsize": cache.currsize},
        "realization_status": "retained_recursive_evaluator_only",
        "lean_equivalence": False,
        "lean_refutation": False,
        "finite_negative_has_proof_credit": False,
    }


def _validated_witness(record):
    if not isinstance(record, dict) or record.get("schema_version") != 1:
        raise ValueError("witness schema_version must be 1")
    if record.get("semantics") not in VERSIONS:
        raise ValueError("witness has unregistered recursion semantics")
    if record.get("domain") != DOMAIN or record.get("generator") != GENERATOR:
        raise ValueError("witness has an unregistered family")
    if record.get("split_rule") != SPLIT_RULE:
        raise ValueError("witness has an unregistered split rule")
    source = record.get("source")
    if not isinstance(source, dict):
        raise ValueError("witness source must be an object")
    a = _integer(source.get("a"), "source.a", low=2, high=20)
    u = _integer(source.get("u"), "source.u", low=2, high=20)
    k = _integer(source.get("k"), "source.k", low=3, high=20)
    if a > k or u > k or source.get("chosen") != "lower":
        raise ValueError("invalid witness source parameters")
    word = _word(source.get("word"))
    maxima = _integer_list(source.get("maxima"), "source.maxima", low=0, high=k - 2,
                           unique=False)
    if len(maxima) != 2 or sorted(token[0] for token in word if token != "S") != [1, 2]:
        raise ValueError("witness source is outside the two-marker family")
    children = tuple(i for i, token in enumerate(word) if token == "S")
    if not 2 <= len(children) <= 8:
        raise ValueError("witness source requires two to eight children")
    layout = record.get("layout")
    if not isinstance(layout, dict):
        raise ValueError("witness layout must be an object")
    keep = _integer_list(layout.get("keep"), "layout.keep", low=0, high=len(word) - 1)
    removed = _integer_list(layout.get("removed"), "layout.removed", low=0, high=len(word) - 1)
    if set(keep) | set(removed) != set(children) or set(keep) & set(removed):
        raise ValueError("witness keep/removed must partition the child positions")
    x = next(i for i, token in enumerate(word) if token != "S" and token[0] == 1)
    y = next(i for i, token in enumerate(word) if token != "S" and token[0] == 2)
    eligible = tuple(q for q in removed if (q < x and y < x) or (x < q and x < y))
    if not eligible or layout.get("p") != keep[0] or layout.get("q") != eligible[0]:
        raise ValueError("witness does not satisfy the registered geometry selection")
    candidate = _candidate({"candidate": record.get("candidate")}, k)
    settings = record.get("evaluator")
    if not isinstance(settings, dict):
        raise ValueError("witness evaluator must be an object")
    cache_size = _integer(settings.get("cache_size"), "evaluator.cache_size", low=1, high=MAX_CACHE_SIZE)
    seconds = _number(settings.get("per_case_seconds"), "evaluator.per_case_seconds",
                      low=0.001, high=MAX_PER_CASE_SECONDS)
    return {
        "semantics": record["semantics"], "source": {"a": a, "u": u, "k": k,
        "chosen": "lower", "word": word, "maxima": maxima}, "keep": keep, "removed": removed,
        "candidate": candidate, "evaluator": {"cache_size": cache_size, "per_case_seconds": seconds},
    }


def replay(record):
    """Recompute a serialized witness from its source and selected split."""
    config = _validated_witness(record)
    source = config["source"]
    rec = evaluator(source["a"], source["u"], source["k"], semantics=config["semantics"],
                    cache_size=config["evaluator"]["cache_size"])
    case = {"children": len(config["keep"]) + len(config["removed"]),
            "runs": sum(token == "S" and (i == 0 or source["word"][i - 1] != "S")
                        for i, token in enumerate(source["word"])),
            "counts": (), "marker_order": (), "word": source["word"], "maxima": source["maxima"],
            "child_positions": tuple(i for i, token in enumerate(source["word"]) if token == "S"),
            "x": next(i for i, token in enumerate(source["word"]) if token != "S" and token[0] == 1),
            "y": next(i for i, token in enumerate(source["word"]) if token != "S" and token[0] == 2),
            "keep": config["keep"], "removed": config["removed"],
            "p": config["keep"][0], "q": record["layout"]["q"]}
    config_for_case = {"source": {key: source[key] for key in ("a", "u", "k", "chosen")},
                       "candidate": config["candidate"]}
    previous_handler = signal.getsignal(signal.SIGALRM)
    signal.signal(signal.SIGALRM, _expired)
    signal.setitimer(signal.ITIMER_REAL, config["evaluator"]["per_case_seconds"])
    try:
        row = _evaluate_case(rec, config_for_case, case, record.get("layout", {}).get("case_index", 0))
    except CaseTimeout:
        return {"replayed": False, "outcome": "timeout", "lean_equivalence": False,
                "lean_refutation": False}
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
    matched = row["target"]["violates_budget"] and row["control"]["passes_next"]
    return {
        "replayed": matched,
        "outcome": "witness_replayed" if matched else "predicate_not_reproduced",
        "computed": {"target": row["target"], "control": row["control"]},
        "source_well_formed_conditions": row["source"]["well_formed_conditions"],
        "realization_status": "retained_recursive_evaluator_only",
        "lean_equivalence": False,
        "lean_refutation": False,
    }
