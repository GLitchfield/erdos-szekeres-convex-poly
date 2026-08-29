from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_factory_v3_pilot import (  # noqa: E402
    BLIND_PROJECTOR_VERSION,
    PROVIDER_POLICY,
    PilotError,
    check_pilot,
    compact_hash,
    recompute_aggregate,
    sha256,
    terminal_for_aggregate,
)


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_text(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


class PilotFixture:
    BASE = "a" * 40
    SENTINEL = "violet quartz heron lantern moss copper orbit velvet prism cedar comet willow"

    def __init__(self, root: Path) -> None:
        self.root = root
        self.run_id = "synthetic-v3-pilot"
        self.common_path = "inputs/common-prompt.md"
        write_text(root / self.common_path, "One common non-memory prompt contract.\n")
        self.common_sha = sha256((root / self.common_path).read_bytes())
        self.context_paths = {
            "M-full": "inputs/context-full-manifest.json",
            "M-sparse": "inputs/context-sparse-manifest.json",
        }
        self.context_visible_paths = {
            "M-full": "inputs/context-full.md",
            "M-sparse": "inputs/context-sparse.md",
        }
        self.triage_paths = {
            "T-free": "inputs/triage-free-contract.json",
            "T-skeleton": "inputs/triage-skeleton-contract.json",
        }
        for policy, path in self.context_paths.items():
            visible = self.context_visible_paths[policy]
            write_text(root / visible, f"Frozen generation-visible context for {policy}.\n")
            inputs = [{"path": visible, "sha256": sha256((root / visible).read_bytes())}]
            write_json(root / path, {
                "schema_version": 1,
                "policy": policy,
                "inputs": inputs,
                "workspace_fingerprint": compact_hash(inputs),
            })
        self.memory_path = self.context_paths["M-full"]
        for policy, path in self.triage_paths.items():
            write_json(root / path, {"schema_version": 1, "policy": policy})
        self.projector_path = "inputs/blind-projector.json"
        write_json(root / self.projector_path, {
            "schema_version": 1,
            "version": BLIND_PROJECTOR_VERSION,
            "payload_fields": sorted({"projector_version", "statement", "neutral_annotation"}),
        })

        self.raw_specs: list[dict[str, str]] = []
        self.raw_payloads: dict[str, dict] = {}
        self.raw_paths: dict[str, str] = {}
        call_policies = [
            ("raw-full-a", "M-full"),
            ("raw-full-b", "M-full"),
            ("raw-sparse-a", "M-sparse"),
            ("raw-sparse-b", "M-sparse"),
        ]
        serial = 0
        for call_id, policy in call_policies:
            output = f"private/{call_id}-private.json"
            result = f"tasks/{call_id}/result.json"
            task = f"tasks/{call_id}/task.json"
            rows = []
            for _ in range(10):
                candidate_id = f"cand-{serial:03d}"
                raw_text = f"Opaque mathematical seed text number {serial:03d} carrying neutral content."
                rows.append({
                    "id": candidate_id,
                    "raw_text": raw_text,
                    "sha256": sha256(raw_text.encode()),
                    "neutral_annotation": f"opaque annotation {serial:03d}",
                    "rejected_title": f"Withheld title {serial:03d}",
                    "family_label": f"withheld-family-label-{serial:03d}",
                    "source_title": f"Withheld source title {serial:03d}",
                    "source_url": f"https://private.invalid/source/{serial:03d}",
                    "private_reasoning": (
                        self.SENTINEL if serial == 0 else f"withheld-reasoning-token-{serial:03d}"
                    ),
                })
                serial += 1
            payload = {
                "schema_version": 1,
                "raw_call_id": call_id,
                "context_policy": policy,
                "common_prompt_sha256": self.common_sha,
                "no_refill": True,
                "replacement_count": 0,
                "attempted_ids": [row["id"] for row in rows],
                "invocation_id": f"invocation-{call_id}",
                "candidates": rows,
            }
            write_json(root / output, payload)
            self.make_task_result(
                task, result, output,
                [self.common_path, self.context_paths[policy], self.context_visible_paths[policy]],
                call_id,
            )
            self.raw_specs.append({
                "id": call_id,
                "context_policy": policy,
                "task": task,
                "task_sha256": sha256((root / task).read_bytes()),
                "result": result,
                "result_sha256": sha256((root / result).read_bytes()),
                "private_output": output,
                "private_output_sha256": sha256((root / output).read_bytes()),
            })
            self.raw_payloads[call_id] = payload
            self.raw_paths[call_id] = output

        self.projection_paths: dict[str, str] = {}
        for replicate in ("A", "B"):
            rows = []
            for call_id, _policy in call_policies:
                source = self.raw_payloads[call_id]["candidates"]
                selected = source[:5] if replicate == "A" else source[5:]
                for raw in selected:
                    rows.append({
                        "candidate_id": raw["id"],
                        "raw_call_id": call_id,
                        "raw_path": self.raw_paths[call_id],
                        "raw_sha256": raw["sha256"],
                        "raw_text": raw["raw_text"],
                        "neutral_annotation": raw["neutral_annotation"],
                    })
            path = f"private/projection-{replicate.lower()}-private.json"
            write_json(root / path, {
                "schema_version": 1,
                "projection_id": f"projection-{replicate.lower()}",
                "replicate": replicate,
                "candidates": rows,
                "workspace_fingerprint": compact_hash(rows),
            })
            self.projection_paths[replicate] = path

        self.eval_specs: list[dict[str, str]] = []
        self.eval_payloads: dict[str, dict] = {}
        self.eval_paths: dict[str, str] = {}
        self.all_eval_rows: list[dict] = []
        eval_grid = [
            ("eval-free-a", "T-free", "A"),
            ("eval-free-b", "T-free", "B"),
            ("eval-skeleton-a", "T-skeleton", "A"),
            ("eval-skeleton-b", "T-skeleton", "B"),
        ]
        blind_serial = 0
        for evaluator_id, policy, replicate in eval_grid:
            rows = []
            source_cursor = 100 if policy == "T-free" else 150
            for raw_index, (call_id, context_policy) in enumerate(call_policies):
                source = self.raw_payloads[call_id]["candidates"]
                selected = source[:5] if replicate == "A" else source[5:]
                for local, raw in enumerate(selected):
                    blind_id = f"blind-{blind_serial:03d}"
                    blind_serial += 1
                    global_index = int(raw["id"].split("-")[1])
                    context_index = global_index if context_policy == "M-full" else global_index - 20
                    target_defect_limit = 4 if context_policy == "M-full" else 5
                    source_duration = (
                        20 if policy == "T-free"
                        else 14 if context_policy == "M-full"
                        else 15
                    )
                    payload = {
                        "projector_version": BLIND_PROJECTOR_VERSION,
                        "statement": raw["raw_text"],
                        "neutral_annotation": raw["neutral_annotation"],
                    }
                    row = {
                        "candidate_id": raw["id"],
                        "raw_path": self.raw_paths[call_id],
                        "raw_sha256": raw["sha256"],
                        "creative_operation": ["lift", "dualize", "encode"][global_index % 3],
                        "model_tier": ["realizable", "order-type", "abstract"][global_index % 3],
                        "family_signature": f"private-family-signature-{global_index:03d}",
                        "first_terminal": "synthetic-terminal",
                        "defect_mask": ["target"] if context_index < target_defect_limit else ["gate"],
                        "stage_reached": "full-card" if context_index < 11 else "source",
                        "source_intervals": [[source_cursor, source_cursor + source_duration]],
                        "skeleton_frozen_at": None if policy == "T-free" else 150,
                        "blind_id": blind_id,
                        "blind_payload": payload,
                        "rejected_title": raw["rejected_title"],
                        "source_title": raw["source_title"],
                        "source_url": raw["source_url"],
                        "private_reasoning": f"evaluation-private-reasoning-{blind_serial:03d}",
                    }
                    source_cursor += source_duration
                    rows.append(row)
                    enriched = copy.deepcopy(row)
                    enriched.update({
                        "context_policy": context_policy,
                        "triage_policy": policy,
                        "replicate": replicate,
                        "evaluator_id": evaluator_id,
                        "source_duration": source_duration,
                        "source_event_count": 1,
                    })
                    self.all_eval_rows.append(enriched)
            output = f"private/{evaluator_id}-private.json"
            result = f"tasks/{evaluator_id}/result.json"
            task = f"tasks/{evaluator_id}/task.json"
            eval_payload = {
                "schema_version": 1,
                "evaluator_id": evaluator_id,
                "triage_policy": policy,
                "replicate": replicate,
                "boundary": [100, 500],
                "projection_sha256": sha256((root / self.projection_paths[replicate]).read_bytes()),
                "invocation_id": f"invocation-{evaluator_id}",
                "candidates": rows,
            }
            write_json(root / output, eval_payload)
            self.make_task_result(
                task, result, output,
                [self.projection_paths[replicate], self.triage_paths[policy]], evaluator_id,
            )
            self.eval_specs.append({
                "id": evaluator_id,
                "triage_policy": policy,
                "replicate": replicate,
                "task": task,
                "task_sha256": sha256((root / task).read_bytes()),
                "result": result,
                "result_sha256": sha256((root / result).read_bytes()),
                "private_output": output,
                "private_output_sha256": sha256((root / output).read_bytes()),
                "projection": self.projection_paths[replicate],
                "projection_sha256": sha256((root / self.projection_paths[replicate]).read_bytes()),
            })
            self.eval_payloads[evaluator_id] = eval_payload
            self.eval_paths[evaluator_id] = output

        self.bundle_path = "private/blind-bundle-private.json"
        self.mapping_path = "private/heldback-mapping-private.json"
        bundle_items = []
        mapping_items = []
        for row in self.all_eval_rows:
            payload_hash = compact_hash(row["blind_payload"])
            bundle_items.append({
                "blind_id": row["blind_id"],
                "payload": row["blind_payload"],
                "payload_sha256": payload_hash,
            })
            mapping_items.append({
                "blind_id": row["blind_id"],
                "evaluator_id": row["evaluator_id"],
                "candidate_id": row["candidate_id"],
                "context_policy": row["context_policy"],
                "triage_policy": row["triage_policy"],
                "evaluation_sha256": payload_hash,
            })
        write_json(root / self.bundle_path, {
            "schema_version": 1,
            "projector_version": BLIND_PROJECTOR_VERSION,
            "items": bundle_items,
        })
        write_json(root / self.mapping_path, {"schema_version": 1, "items": mapping_items})

        self.auditor_specs: list[dict[str, str]] = []
        self.audit_payloads: dict[str, dict] = {}
        self.audit_paths: dict[str, str] = {}
        for auditor_id in ("auditor-alpha", "auditor-beta"):
            output = f"private/{auditor_id}-private.json"
            result = f"tasks/{auditor_id}/result.json"
            task = f"tasks/{auditor_id}/task.json"
            decisions = []
            for row in self.all_eval_rows:
                global_index = int(row["candidate_id"].split("-")[1])
                context_index = global_index if row["context_policy"] == "M-full" else global_index - 20
                eligible_limit = 10 if row["context_policy"] == "M-full" else 14
                # Exactly one arm can establish each counted family signature.
                eligible = row["triage_policy"] == "T-free" and context_index < eligible_limit
                decisions.append({
                    "blind_id": row["blind_id"],
                    "status": "eligible" if eligible else "rejected",
                })
            payload = {
                "schema_version": 1,
                "auditor_id": auditor_id,
                "bundle_sha256": sha256((root / self.bundle_path).read_bytes()),
                "invocation_id": f"invocation-{auditor_id}",
                "decisions": decisions,
            }
            write_json(root / output, payload)
            self.make_task_result(
                task, result, output,
                [self.bundle_path, self.memory_path, self.context_visible_paths["M-full"]],
                auditor_id,
                # The descriptor and every committed full-memory input are frozen.
                profile="research_card_auditor",
            )
            self.auditor_specs.append({
                "id": auditor_id,
                "task": task,
                "task_sha256": sha256((root / task).read_bytes()),
                "result": result,
                "result_sha256": sha256((root / result).read_bytes()),
                "private_output": output,
                "private_output_sha256": sha256((root / output).read_bytes()),
            })
            self.audit_payloads[auditor_id] = payload
            self.audit_paths[auditor_id] = output

        self.invocations: list[dict] = []
        staged_specs = [
            *(("raw", spec) for spec in self.raw_specs),
            *(("evaluator", spec) for spec in self.eval_specs),
            *(("auditor", spec) for spec in self.auditor_specs),
        ]
        for index, (stage, spec) in enumerate(staged_specs):
            call_id = spec["id"]
            transcript = f"private/transcript-{index:02d}-private.json"
            invocation_id = f"invocation-{call_id}"
            session_id = f"session-{index:02d}"
            completion_sha = sha256(f"opaque completion {index:02d}".encode())
            write_json(root / transcript, {
                "schema_version": 1,
                "invocation_id": invocation_id,
                "session_id": session_id,
                "output_sha256": spec["private_output_sha256"],
                "completion_sha256": completion_sha,
            })
            task_payload = json.loads((root / spec["task"]).read_text())
            self.invocations.append({
                "call_id": call_id,
                "stage": stage,
                "invocation_id": invocation_id,
                "session_id": session_id,
                "provider_policy": PROVIDER_POLICY,
                "start_event": 1000 + 10 * index,
                "end_event": 1005 + 10 * index,
                "transcript_path": transcript,
                "transcript_sha256": sha256((root / transcript).read_bytes()),
                "completion_sha256": completion_sha,
                "task_sha256": spec["task_sha256"],
                "result_sha256": spec["result_sha256"],
                "output_sha256": spec["private_output_sha256"],
                "input_fingerprint": task_payload["workspace_fingerprint"],
                "parent_input_fingerprint": task_payload["workspace_fingerprint"],
            })

        self.aggregate_path = "public/aggregate-public.json"
        self.future_path = "future/packet-manifest.json"
        write_json(root / self.aggregate_path, self.expected_aggregate())
        all_results = [
            *(spec["result"] for spec in self.raw_specs),
            *(spec["result"] for spec in self.eval_specs),
            *(spec["result"] for spec in self.auditor_specs),
        ]
        write_json(
            root / self.future_path,
            {
                "schema_version": 1,
                "entries": [
                    {"path": path, "sha256": sha256((root / path).read_bytes())}
                    for path in all_results
                ],
            },
        )
        self.design = {
            "schema_version": 1,
            "run_id": self.run_id,
            "base_revision": self.BASE,
            "common_prompt_sha256": self.common_sha,
            "common_prompt": self.common_path,
            "context_manifests": {
                policy: {
                    "path": path,
                    "sha256": sha256((root / path).read_bytes()),
                }
                for policy, path in self.context_paths.items()
            },
            "triage_contracts": {
                policy: {
                    "path": path,
                    "sha256": sha256((root / path).read_bytes()),
                }
                for policy, path in self.triage_paths.items()
            },
            "private_globs": ["private/**"],
            "raw_calls": self.raw_specs,
            "evaluators": self.eval_specs,
            "blind_projector": {
                "path": self.projector_path,
                "sha256": sha256((root / self.projector_path).read_bytes()),
                "version": BLIND_PROJECTOR_VERSION,
            },
            "blind_bundle": self.bundle_path,
            "blind_bundle_sha256": sha256((root / self.bundle_path).read_bytes()),
            "heldback_mapping": self.mapping_path,
            "heldback_mapping_sha256": sha256((root / self.mapping_path).read_bytes()),
            "full_memory_manifest": {
                "path": self.memory_path,
                "sha256": sha256((root / self.memory_path).read_bytes()),
            },
            "auditors": self.auditor_specs,
            "invocations": self.invocations,
            "public_aggregate": self.aggregate_path,
            "public_aggregate_sha256": sha256((root / self.aggregate_path).read_bytes()),
            "public_paths": [*all_results, self.aggregate_path],
            "future_manifest": self.future_path,
            "future_manifest_sha256": sha256((root / self.future_path).read_bytes()),
        }
        self.design_path = root / "design.json"
        self.save_design()

    def make_task_result(
        self, task_path: str, result_path: str, output_path: str, inputs: list[str], task_id: str,
        *, profile: str = "research_question_generator",
    ) -> None:
        input_entries = [
            {"path": path, "sha256": sha256((self.root / path).read_bytes())} for path in inputs
        ]
        task = {
            "schema_version": 1,
            "run_id": self.run_id,
            "task_id": task_id,
            "wayfinder_ticket": "docs/wayfinder/tickets/synthetic.md",
            "profile": profile,
            "base_revision": self.BASE,
            "workspace_fingerprint": compact_hash(input_entries),
            "objective": "Exercise one frozen synthetic pilot stage.",
            "theorem_contract": None,
            "inputs": input_entries,
            "ownership": {"read_paths": inputs, "write_paths": [output_path, result_path]},
            "budget": {
                "wall_minutes": 1, "cpu_cores": 1, "memory_gib": 1, "output_gib": 0.01
            },
            "deliverables": [output_path, result_path],
            "required_checks": ["authenticate inputs"],
            "success": ["terminal aggregate-only result"],
            "stop": ["no adaptive refill"],
            "claims_allowed": ["proposal"],
        }
        result = {
            "schema_version": 1,
            "task_id": task_id,
            "status": "completed",
            "claim_level": "proposal",
            "summary": "Aggregate-only synthetic task completion.",
            "supports": ["instrumentation fixture"],
            "does_not_support": ["mathematical progress"],
            "changes": [output_path, result_path],
            "checks": [{"command": "synthetic fixture", "outcome": "passed"}],
            "evidence": ["aggregate-only"],
            "limitations": ["synthetic"],
            "blocked_by": [],
        }
        write_json(self.root / task_path, task)
        write_json(self.root / result_path, result)

    def expected_aggregate(self) -> dict:
        decisions = []
        for auditor_id in ("auditor-alpha", "auditor-beta"):
            decisions.append({d["blind_id"]: d["status"] for d in self.audit_payloads[auditor_id]["decisions"]})
        status = {
            blind_id: decisions[0][blind_id]
            if decisions[0][blind_id] == decisions[1][blind_id]
            else "unresolved"
            for blind_id in decisions[0]
        }
        return recompute_aggregate(self.all_eval_rows, status)

    def save_design(self) -> None:
        write_json(self.design_path, self.design)

    def save_raw(self, call_id: str) -> None:
        write_json(self.root / self.raw_paths[call_id], self.raw_payloads[call_id])
        spec = next(spec for spec in self.raw_specs if spec["id"] == call_id)
        spec["private_output_sha256"] = sha256((self.root / spec["private_output"]).read_bytes())
        self.refresh_invocation(call_id)
        self.save_design()

    def save_eval(self, evaluator_id: str) -> None:
        write_json(self.root / self.eval_paths[evaluator_id], self.eval_payloads[evaluator_id])
        spec = next(spec for spec in self.eval_specs if spec["id"] == evaluator_id)
        spec["private_output_sha256"] = sha256((self.root / spec["private_output"]).read_bytes())
        self.refresh_invocation(evaluator_id)
        self.save_design()

    def save_audit(self, auditor_id: str) -> None:
        write_json(self.root / self.audit_paths[auditor_id], self.audit_payloads[auditor_id])
        spec = next(spec for spec in self.auditor_specs if spec["id"] == auditor_id)
        spec["private_output_sha256"] = sha256((self.root / spec["private_output"]).read_bytes())
        self.refresh_invocation(auditor_id)
        self.save_design()

    def refresh_invocation(self, call_id: str) -> None:
        specs = [*self.raw_specs, *self.eval_specs, *self.auditor_specs]
        spec = next(spec for spec in specs if spec["id"] == call_id)
        record = next(record for record in self.invocations if record["call_id"] == call_id)
        task = json.loads((self.root / spec["task"]).read_text())
        record.update({
            "task_sha256": spec["task_sha256"],
            "result_sha256": spec["result_sha256"],
            "output_sha256": spec["private_output_sha256"],
            "input_fingerprint": task["workspace_fingerprint"],
            "parent_input_fingerprint": task["workspace_fingerprint"],
        })
        transcript_path = self.root / record["transcript_path"]
        transcript = json.loads(transcript_path.read_text())
        transcript["output_sha256"] = spec["private_output_sha256"]
        write_json(transcript_path, transcript)
        record["transcript_sha256"] = sha256(transcript_path.read_bytes())

    def rewrite_task_inputs(self, spec: dict, inputs: list[str]) -> None:
        task_path = self.root / spec["task"]
        task = json.loads(task_path.read_text())
        entries = [
            {"path": path, "sha256": sha256((self.root / path).read_bytes())} for path in inputs
        ]
        task["inputs"] = entries
        task["ownership"]["read_paths"] = inputs
        task["workspace_fingerprint"] = compact_hash(entries)
        write_json(task_path, task)
        spec["task_sha256"] = sha256(task_path.read_bytes())
        self.refresh_invocation(spec["id"])
        self.save_design()

    def rewrite_public_result(self, spec: dict, text: str) -> None:
        result_path = self.root / spec["result"]
        result = json.loads(result_path.read_text())
        result["summary"] += " " + text
        write_json(result_path, result)
        spec["result_sha256"] = sha256(result_path.read_bytes())
        self.refresh_invocation(spec["id"])
        manifest_path = self.root / self.future_path
        manifest = json.loads(manifest_path.read_text())
        entry = next(item for item in manifest["entries"] if item["path"] == spec["result"])
        entry["sha256"] = sha256(result_path.read_bytes())
        write_json(manifest_path, manifest)
        self.design["future_manifest_sha256"] = sha256(manifest_path.read_bytes())
        self.save_design()

    def refresh_aggregate(self) -> None:
        write_json(self.root / self.aggregate_path, self.expected_aggregate())
        self.design["public_aggregate_sha256"] = sha256(
            (self.root / self.aggregate_path).read_bytes()
        )
        self.save_design()


def emit_canary_suite(root: Path) -> dict[str, dict[str, object]]:
    if root.exists():
        raise FileExistsError(f"refusing to overwrite existing canary suite: {root}")
    root.mkdir(parents=True)
    oracle: dict[str, dict[str, object]] = {}

    valid = PilotFixture(root / "valid")
    oracle["valid"] = {
        "exit": 0,
        "terminal": "V3_CANARY_VALID",
        "aggregate": valid.expected_aggregate(),
    }

    fork = PilotFixture(root / "fork-drift")
    fork.eval_payloads["eval-skeleton-a"]["candidates"][0]["raw_sha256"] = "0" * 64
    fork.save_eval("eval-skeleton-a")
    oracle["fork-drift"] = {"exit": 1, "terminal": "V3E_FORK_RAW_MISMATCH"}

    duplicate = PilotFixture(root / "duplicate-refill")
    duplicate.raw_payloads["raw-full-a"]["candidates"][1]["id"] = (
        duplicate.raw_payloads["raw-full-a"]["candidates"][0]["id"]
    )
    duplicate.save_raw("raw-full-a")
    oracle["duplicate-refill"] = {
        "exit": 1,
        "terminal": "V3E_RAW_ID_DUPLICATE_OR_REFILL",
    }

    allocation = PilotFixture(root / "allocation-imbalance")
    replacement = copy.deepcopy(allocation.raw_payloads["raw-full-b"]["candidates"][5])
    row = allocation.eval_payloads["eval-free-a"]["candidates"][0]
    row["candidate_id"] = replacement["id"]
    row["raw_path"] = allocation.raw_paths["raw-full-b"]
    row["raw_sha256"] = replacement["sha256"]
    row["blind_payload"] = {
        "projector_version": BLIND_PROJECTOR_VERSION,
        "statement": replacement["raw_text"],
        "neutral_annotation": replacement["neutral_annotation"],
    }
    allocation.save_eval("eval-free-a")
    oracle["allocation-imbalance"] = {
        "exit": 1,
        "terminal": "V3E_EVALUATOR_ALLOCATION_IMBALANCE",
    }

    disagreement = PilotFixture(root / "auditor-disagreement")
    disagreement.audit_payloads["auditor-beta"]["decisions"][0]["status"] = "rejected"
    disagreement.save_audit("auditor-beta")
    disagreement.refresh_aggregate()
    oracle["auditor-disagreement"] = {
        "exit": 0,
        "terminal": "V3U_AUDITOR_DISAGREEMENT",
        "aggregate": disagreement.expected_aggregate(),
    }

    timing = PilotFixture(root / "timing-overlap")
    timing.eval_payloads["eval-free-a"]["candidates"][0]["source_intervals"] = [
        [100, 105], [104, 106]
    ]
    timing.save_eval("eval-free-a")
    oracle["timing-overlap"] = {
        "exit": 1,
        "terminal": "V3E_SOURCE_INTERVAL_OVERLAP",
    }

    leak = PilotFixture(root / "public-sentinel")
    leak.rewrite_public_result(leak.raw_specs[0], leak.SENTINEL)
    oracle["public-sentinel"] = {
        "exit": 1,
        "terminal": "V3E_PUBLIC_PRIVATE_TEXT_LEAK",
    }

    private_manifest = PilotFixture(root / "private-manifest")
    manifest_path = private_manifest.root / private_manifest.future_path
    manifest = json.loads(manifest_path.read_text())
    private_path = private_manifest.raw_specs[0]["private_output"]
    manifest["entries"].append({
        "path": private_path,
        "sha256": sha256((private_manifest.root / private_path).read_bytes()),
    })
    write_json(manifest_path, manifest)
    private_manifest.design["future_manifest_sha256"] = sha256(manifest_path.read_bytes())
    private_manifest.save_design()
    oracle["private-manifest"] = {
        "exit": 1,
        "terminal": "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST",
    }

    write_json(root / "suite-oracle.json", {"schema_version": 1, "fixtures": oracle})
    return oracle


class CheckPilotTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.fixture = PilotFixture(self.root)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def check(self) -> dict:
        return check_pilot(self.root, self.fixture.design_path)

    def test_valid_exact_forty_to_eighty_pilot(self) -> None:
        result = self.check()
        self.assertEqual(result["raw_count"], 40)
        self.assertEqual(result["evaluation_count"], 80)
        self.assertEqual(result["audited_count"], 80)
        self.assertEqual(result["unresolved_count"], 0)
        self.assertEqual(terminal_for_aggregate(result), "V3_CANARY_VALID")
        self.assertEqual(
            result["by_context"]["M-full"]["eligible_noncolliding_family_signatures"], 10
        )
        self.assertEqual(
            result["by_context"]["M-sparse"]["eligible_noncolliding_family_signatures"], 14
        )
        self.assertEqual(
            result["by_context"]["M-full"]["target_producer_consumer_defect_count"], 8
        )
        self.assertEqual(
            result["by_context"]["M-sparse"]["target_producer_consumer_defect_count"], 10
        )
        self.assertEqual(
            result["by_cell"]["M-full"]["T-free"]["defective_source_duration"], 400
        )
        self.assertEqual(
            result["by_cell"]["M-full"]["T-skeleton"]["defective_source_duration"], 280
        )
        self.assertEqual(
            result["by_cell"]["M-sparse"]["T-free"]["defective_source_duration"], 400
        )
        self.assertEqual(
            result["by_cell"]["M-sparse"]["T-skeleton"]["defective_source_duration"], 300
        )
        for context in ("M-full", "M-sparse"):
            for triage in ("T-free", "T-skeleton"):
                self.assertEqual(result["by_cell"][context][triage]["full_card_count"], 11)
                self.assertEqual(result["by_cell"][context][triage]["source_event_count"], 20)
        self.assertEqual(result["source_event_count"], 80)
        self.assertEqual(
            result["threshold_inputs"]["sparse_minus_full_distinct_family_delta"], 4
        )
        self.assertEqual(result["threshold_inputs"]["sparse_minus_full_defect_delta"], 2)
        self.assertEqual(result["threshold_inputs"]["source_duration_saved_numerator"], 220)
        self.assertEqual(result["threshold_inputs"]["source_duration_free_denominator"], 800)
        self.assertEqual(result["threshold_outcomes"]["memory_policy"], "M-sparse-signal")
        self.assertEqual(result["threshold_outcomes"]["skeleton_policy"], "T-skeleton-signal")

    def test_emitted_canary_suite_matches_exact_oracle(self) -> None:
        suite_root = self.root / "suite"
        oracle = emit_canary_suite(suite_root)
        for name, expected in oracle.items():
            fixture_root = suite_root / name
            design = fixture_root / "design.json"
            if expected["exit"] == 0:
                aggregate = check_pilot(fixture_root, design)
                self.assertEqual(terminal_for_aggregate(aggregate), expected["terminal"])
                self.assertEqual(aggregate, expected["aggregate"])
            else:
                with self.assertRaises(PilotError) as caught:
                    check_pilot(fixture_root, design)
                self.assertEqual(caught.exception.code, expected["terminal"])

    def test_fork_sha_drift_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-skeleton-a"]
        payload["candidates"][0]["raw_sha256"] = "0" * 64
        self.fixture.save_eval("eval-skeleton-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_FORK_RAW_MISMATCH")

    def test_duplicate_or_refill_raw_id_fails(self) -> None:
        payload = self.fixture.raw_payloads["raw-full-a"]
        payload["candidates"][1]["id"] = payload["candidates"][0]["id"]
        self.fixture.save_raw("raw-full-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_RAW_ID_DUPLICATE_OR_REFILL")

    def test_four_six_five_five_allocation_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-free-a"]
        replacement = copy.deepcopy(self.fixture.raw_payloads["raw-full-b"]["candidates"][5])
        row = payload["candidates"][0]
        row["candidate_id"] = replacement["id"]
        row["raw_path"] = self.fixture.raw_paths["raw-full-b"]
        row["raw_sha256"] = replacement["sha256"]
        row["blind_payload"] = {
            "projector_version": BLIND_PROJECTOR_VERSION,
            "statement": replacement["raw_text"],
            "neutral_annotation": replacement["neutral_annotation"],
        }
        self.fixture.save_eval("eval-free-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_EVALUATOR_ALLOCATION_IMBALANCE")

    def test_auditor_disagreement_is_unresolved_and_not_novel(self) -> None:
        before = self.fixture.expected_aggregate()
        first = self.fixture.audit_payloads["auditor-beta"]["decisions"][0]
        self.assertEqual(first["status"], "eligible")
        first["status"] = "rejected"
        self.fixture.save_audit("auditor-beta")
        self.fixture.refresh_aggregate()
        after = self.check()
        self.assertEqual(after["unresolved_count"], 1)
        self.assertEqual(after["eligible_count"], before["eligible_count"] - 1)
        self.assertEqual(
            after["by_context"]["M-full"]["eligible_noncolliding_family_signatures"],
            before["by_context"]["M-full"]["eligible_noncolliding_family_signatures"] - 1,
        )
        self.assertEqual(terminal_for_aggregate(after), "V3U_AUDITOR_DISAGREEMENT")

    def test_negative_timing_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-free-a"]
        payload["candidates"][0]["source_intervals"] = [[-1, 2]]
        self.fixture.save_eval("eval-free-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_SOURCE_INTERVAL_INVALID")

    def test_overlapping_candidate_local_timing_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-free-a"]
        payload["candidates"][0]["source_intervals"] = [[200, 205], [204, 206]]
        self.fixture.save_eval("eval-free-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_SOURCE_INTERVAL_OVERLAP")

    def test_pre_freeze_skeleton_source_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-skeleton-a"]
        payload["candidates"][0]["source_intervals"] = [[140, 145]]
        self.fixture.save_eval("eval-skeleton-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_SOURCE_INTERVAL_INVALID")

    def test_unique_private_sentinel_leak_fails(self) -> None:
        sentinel = self.fixture.SENTINEL
        result_path = self.root / self.fixture.raw_specs[0]["result"]
        result = json.loads(result_path.read_text())
        result["summary"] += " " + sentinel
        write_json(result_path, result)
        self.fixture.raw_specs[0]["result_sha256"] = sha256(result_path.read_bytes())
        self.fixture.refresh_invocation(self.fixture.raw_specs[0]["id"])
        manifest_path = self.root / self.fixture.future_path
        manifest = json.loads(manifest_path.read_text())
        entry = next(item for item in manifest["entries"] if item["path"] == self.fixture.raw_specs[0]["result"])
        entry["sha256"] = sha256(result_path.read_bytes())
        write_json(manifest_path, manifest)
        self.fixture.design["future_manifest_sha256"] = sha256(manifest_path.read_bytes())
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_PUBLIC_PRIVATE_TEXT_LEAK")
        self.assertNotIn(sentinel, str(caught.exception))

    def test_private_path_in_future_manifest_fails(self) -> None:
        manifest = json.loads((self.root / self.fixture.future_path).read_text())
        manifest["entries"].append({"path": self.fixture.raw_specs[0]["private_output"]})
        write_json(self.root / self.fixture.future_path, manifest)
        self.fixture.design["future_manifest_sha256"] = sha256(
            (self.root / self.fixture.future_path).read_bytes()
        )
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST")
        self.assertNotIn(self.fixture.raw_specs[0]["private_output"], str(caught.exception))

    def test_sparse_raw_task_rejects_extra_full_context(self) -> None:
        spec = next(spec for spec in self.fixture.raw_specs if spec["id"] == "raw-sparse-a")
        task = json.loads((self.root / spec["task"]).read_text())
        inputs = [item["path"] for item in task["inputs"]]
        inputs += [
            self.fixture.context_paths["M-full"],
            self.fixture.context_visible_paths["M-full"],
        ]
        self.fixture.rewrite_task_inputs(spec, inputs)
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_STAGE_INPUT_SET_MISMATCH")

    def test_evaluator_rejects_authenticated_all_forty_projection(self) -> None:
        path = self.root / self.fixture.projection_paths["A"]
        projection = json.loads(path.read_text())
        rows = []
        for call_id, raw_payload in self.fixture.raw_payloads.items():
            for raw in raw_payload["candidates"]:
                rows.append({
                    "candidate_id": raw["id"],
                    "raw_call_id": call_id,
                    "raw_path": self.fixture.raw_paths[call_id],
                    "raw_sha256": raw["sha256"],
                    "raw_text": raw["raw_text"],
                    "neutral_annotation": raw["neutral_annotation"],
                })
        projection["candidates"] = rows
        projection["workspace_fingerprint"] = compact_hash(rows)
        write_json(path, projection)
        new_hash = sha256(path.read_bytes())
        for spec in self.fixture.eval_specs:
            if spec["replicate"] == "A":
                spec["projection_sha256"] = new_hash
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_EVALUATOR_PROJECTION_MISMATCH")

    def test_auditor_rejects_heldback_mapping_input(self) -> None:
        spec = self.fixture.auditor_specs[0]
        task = json.loads((self.root / spec["task"]).read_text())
        inputs = [item["path"] for item in task["inputs"]] + [self.fixture.mapping_path]
        self.fixture.rewrite_task_inputs(spec, inputs)
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_STAGE_INPUT_SET_MISMATCH")

    def test_normalized_arm_label_in_blind_payload_fails(self) -> None:
        bundle_path = self.root / self.fixture.bundle_path
        bundle = json.loads(bundle_path.read_text())
        bundle["items"][0]["payload"]["neutral_annotation"] = "m-FULL"
        bundle["items"][0]["payload_sha256"] = compact_hash(bundle["items"][0]["payload"])
        write_json(bundle_path, bundle)
        self.fixture.design["blind_bundle_sha256"] = sha256(bundle_path.read_bytes())
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_BLIND_PAYLOAD_INVALID")
        self.assertNotIn("m-FULL", str(caught.exception))

    def test_nested_auditor_private_leaf_in_public_result_fails(self) -> None:
        protected = self.fixture.audit_payloads["auditor-alpha"]["decisions"][0]["blind_id"]
        self.fixture.rewrite_public_result(self.fixture.auditor_specs[0], protected)
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_PUBLIC_PRIVATE_TEXT_LEAK")
        self.assertNotIn(protected, str(caught.exception))

    def test_private_path_in_future_manifest_metadata_fails(self) -> None:
        path = self.root / self.fixture.future_path
        manifest = json.loads(path.read_text())
        protected = self.fixture.raw_specs[0]["private_output"]
        manifest["metadata"] = {"note": protected.upper()}
        write_json(path, manifest)
        self.fixture.design["future_manifest_sha256"] = sha256(path.read_bytes())
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST")
        self.assertNotIn(protected, str(caught.exception))

    def test_future_manifest_resolved_alias_to_private_fails(self) -> None:
        alias = self.root / "future/public-looking.json"
        alias.symlink_to((self.root / self.fixture.raw_specs[0]["private_output"]).resolve())
        path = self.root / self.fixture.future_path
        manifest = json.loads(path.read_text())
        manifest["entries"].append({
            "path": "future/public-looking.json",
            "sha256": sha256(alias.read_bytes()),
        })
        write_json(path, manifest)
        self.fixture.design["future_manifest_sha256"] = sha256(path.read_bytes())
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_PRIVATE_PATH_IN_FUTURE_MANIFEST")

    def test_cross_candidate_source_overlap_fails(self) -> None:
        payload = self.fixture.eval_payloads["eval-free-a"]
        payload["candidates"][1]["source_intervals"] = copy.deepcopy(
            payload["candidates"][0]["source_intervals"]
        )
        self.fixture.save_eval("eval-free-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_SOURCE_INTERVAL_OVERLAP")

    def test_reused_invocation_provenance_fails(self) -> None:
        first, second = self.fixture.design["invocations"][-2:]
        second["invocation_id"] = first["invocation_id"]
        second["session_id"] = first["session_id"]
        second["transcript_sha256"] = first["transcript_sha256"]
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_INVOCATION_PROVENANCE_INVALID")

    def test_duplicate_json_key_fails_closed(self) -> None:
        aggregate_path = self.root / self.fixture.aggregate_path
        text = aggregate_path.read_text()
        text = text.replace("{\n", "{\n  \"schema_version\": 999,\n", 1)
        write_text(aggregate_path, text)
        self.fixture.design["public_aggregate_sha256"] = sha256(aggregate_path.read_bytes())
        self.fixture.save_design()
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_SCHEMA_INVALID")

    def test_duplicate_task_input_fails_exact_set(self) -> None:
        spec = self.fixture.raw_specs[0]
        task = json.loads((self.root / spec["task"]).read_text())
        inputs = [item["path"] for item in task["inputs"]]
        self.fixture.rewrite_task_inputs(spec, [*inputs, inputs[0]])
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertEqual(caught.exception.code, "V3E_STAGE_INPUT_SET_MISMATCH")

    def test_cli_and_direct_errors_never_echo_protected_candidate(self) -> None:
        protected = self.fixture.raw_payloads["raw-full-a"]["candidates"][0]["id"]
        self.fixture.raw_payloads["raw-full-a"]["candidates"][0]["sha256"] = "0" * 64
        self.fixture.save_raw("raw-full-a")
        with self.assertRaises(PilotError) as caught:
            self.check()
        self.assertNotIn(protected, str(caught.exception))
        completed = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve().parent / "check_factory_v3_pilot.py"),
                "--repo-root", str(self.root),
                "--design", str(self.fixture.design_path),
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(completed.stderr, "")
        self.assertNotIn(protected, completed.stdout)
        self.assertRegex(completed.stdout.strip(), r"^V3E_[A-Z_]+$")


if __name__ == "__main__":
    unittest.main()
