from __future__ import annotations

import json
from pathlib import Path

import pytest

from es import artifacts, gitutil, usage
from es.errors import CheckFailed, UsageError
from es.jobs import submit, submit_run
from es.run_review import build_review
from es.store import Store


def _event(response_id: str, at: str, *, input_tokens: int, output_tokens: int) -> dict:
    values = {
        "input_tokens": input_tokens,
        "cached_input_tokens": input_tokens // 2,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": output_tokens // 2,
    }
    return {
        "timestamp": at,
        "type": "token_usage_record",
        "payload": {
            "thread_id": "thread-review",
            "response_id": response_id,
            "usage": values,
            "thread_token_usage": values,
        },
    }


def _run(cfg, project: Path, *, records: list[dict] | None = None) -> tuple[Path, dict]:
    out = project / "runs" / "native" / "host"
    out.mkdir(parents=True)
    window = usage.begin(cfg, "codex:researcher", "review test")
    with Store(cfg) as store:
        store.conn.execute(
            "UPDATE research_windows SET started_at=?,ended_at=?,status='complete' WHERE id=?",
            ("2026-01-01T00:00:00+00:00", "2026-01-01T00:10:00+00:00", window),
        )
    source = out / "thread.jsonl"
    events = [{"timestamp": "2026-01-01T00:00:00Z", "type": "session_meta", "payload": {"id": "thread-review"}}]
    events.extend(records or [])
    source.write_text("".join(json.dumps(event) + "\n" for event in events))
    state = {
        "schema_version": 1,
        "status": "complete",
        "phase": "complete",
        "created_at": "2026-01-01T00:00:00Z",
        "updated_at": "2026-01-01T00:15:00Z",
        "root": str(project.resolve()),
        "primary_root": str(project.resolve()),
        "out": str(out.resolve()),
        "model": "gpt-5.6-sol",
        "effort": "xhigh",
        "researcher_agent": "codex:researcher",
        "coordinator_agent": "codex:coordinator",
        "thread_id": "thread-review",
        "thread_path": str(source),
        "window_id": window,
        "baseline_commit": gitutil.head_sha(cfg),
        "host_job_ids": [],
        "timing": {
            "started_at": "2026-01-01T00:00:00Z",
            "finalization_start_at": "2026-01-01T00:05:00Z",
            "deadline_at": "2026-01-01T00:10:00Z",
            "final_deadline_at": "2026-01-01T00:40:00Z",
        },
        "goal": {"status": "complete", "tokensUsed": 12},
        "progress": {"turns_started": 2, "turns_completed": 2},
        "submissions": {},
    }
    (out / "agent-run.json").write_text(json.dumps(state))
    return out, state


def _full(cfg, summary: dict) -> dict:
    return json.loads(artifacts.read(cfg, summary["artifact"]["id"]))


def test_late_same_thread_usage_is_included_once_and_review_is_repeatable(cfg, project):
    inside = _event("response-window", "2026-01-01T00:05:00Z", input_tokens=10, output_tokens=6)
    duplicate = json.loads(json.dumps(inside))
    late = _event("response-late", "2026-01-01T00:20:00Z", input_tokens=8, output_tokens=4)
    out, _state = _run(cfg, project, records=[inside, duplicate, late])

    first = build_review(cfg, out)
    second = build_review(cfg, out)
    full = _full(cfg, first)

    assert first["artifact"]["id"] == second["artifact"]["id"]
    assert first["counts"]["responses"] == 2
    assert first["counts"]["late_responses"] == 1
    assert first["usage"]["output_tokens"] == 10
    assert [record["response_id"] for record in full["usage"]["records"]] == ["response-window", "response-late"]
    assert full["usage"]["records"][1]["boundary"] == "late_same_native_thread"


def test_direct_unlinked_research_jobs_are_counted_and_host_is_excluded(cfg, project):
    out, state = _run(cfg, project)
    direct = submit_run(
        cfg, command=["true"], why="direct research", outputs=["runs/direct.txt"],
        agent=state["researcher_agent"], memory_max="1G", queue=True,
    )
    host = submit_run(
        cfg, command=["true"], why="host", outputs=["runs/host.txt"],
        agent=state["coordinator_agent"], memory_max="1G", queue=True,
    )
    state["host_job_ids"] = [host["id"]]
    (out / "agent-run.json").write_text(json.dumps(state))
    with Store(cfg) as store:
        store.claim("TCore.direct", state["researcher_agent"], 1, "review pending")

    summary = build_review(cfg, out)
    full = _full(cfg, summary)

    assert summary["counts"]["jobs"] == 1
    assert summary["counts"]["pending_jobs"] == 1
    assert summary["counts"]["active_claims"] == 1
    assert full["jobs"][0]["id"] == direct["id"]
    assert full["jobs"][0]["operation_id"] is None
    assert host["id"] not in {job["id"] for job in full["jobs"]}


def test_logs_are_not_copied_summary_is_bounded_and_exit_zero_gets_no_proof_credit(cfg, project):
    out, state = _run(cfg, project)
    checked = submit(cfg, kind="check", node="TCore.direct", argv=["check", "TCore.direct"],
                     agent=state["researcher_agent"], queue=True)
    marker = "PRIVATE-LOG-MARKER-" + "x" * 100_000
    Path(checked["log_path"]).write_text(marker)
    with Store(cfg) as store:
        store.job_update(checked["id"], status="done", exit_code=0, result_json=json.dumps({
            "ok": True, "tail": [marker], "artifact": {"id": "a" * 64, "diagnostic": marker},
        }))
    secret = "supersecretvalue"
    inline = submit_run(
        cfg,
        command=["python3", "-c", "TOKEN='" + secret + "'\nprint('review')"],
        why="inspect inline code", outputs=["runs/inline.txt"], agent=state["researcher_agent"],
        memory_max="1G", queue=True,
    )
    (out / "trial.py").write_text("print('artifact')\n")
    (project / "TCore" / "Basic.lean").write_text("theorem foo : True := by trivial\n")

    summary = build_review(cfg, out)
    encoded = json.dumps(summary, indent=2).encode()
    artifact_data = artifacts.read(cfg, summary["artifact"]["id"])
    full = json.loads(artifact_data)

    assert len(encoded) <= 4096
    assert marker.encode() not in artifact_data
    assert secret.encode() not in artifact_data
    assert summary["counts"]["explicit_proof_receipts"] == 0
    assert summary["theorem_credit"] == "not_inferred"
    assert full["validation"]["evidence"][0]["exit_code"] == 0
    assert full["validation"]["evidence"][0]["explicit_proof_accepted"] is False
    assert {item["path"] for item in full["code_inventory"]["artifact_scripts"]} == {"runs/native/host/trial.py"}
    assert "TCore/Basic.lean" in {item["path"] for item in full["code_inventory"]["changed_tracked_scripts"]}
    assert full["code_inventory"]["inline_commands"][0]["job_id"] == inline["id"]
    assert "<redacted>" in full["code_inventory"]["inline_commands"][0]["sanitized_source"]
    assert summary["code_review_required"] is True
    assert summary["final_review_required"] is True
    assert summary["review_required"] is True


def test_explicit_parent_artifact_root_is_scanned_and_missing_root_reports_limit(cfg, project):
    out, state = _run(cfg, project)
    parent_script = out.parent / "analysis.py"
    parent_script.write_text("print('parent artifact')\n")

    limited = build_review(cfg, out)
    limited_full = _full(cfg, limited)
    assert limited_full["code_inventory"]["artifact_scripts"] == []
    assert limited_full["code_inventory"]["artifact_boundary"]["coverage"] == "host_out_only"
    assert "not inventoried" in limited_full["code_inventory"]["artifact_boundary"]["limitation"]
    assert limited["code_review_required"] is False
    assert limited["final_review_required"] is True

    state["artifact_root"] = str(out.parent)
    (out / "agent-run.json").write_text(json.dumps(state))
    complete = build_review(cfg, out)
    complete_full = _full(cfg, complete)
    assert {item["path"] for item in complete_full["code_inventory"]["artifact_scripts"]} == {
        "runs/native/analysis.py"
    }
    assert complete_full["code_inventory"]["artifact_boundary"] == {
        "coverage": "explicit_artifact_root", "root": "runs/native", "source": "agent-run state",
    }


def test_direct_run_es_validation_is_evidence_without_proof_credit_and_nonfinite_values_drop(cfg, project):
    out, state = _run(cfg, project)
    checked = submit_run(
        cfg, command=["es", "--json", "check", "TCore.direct"], why="record direct check",
        outputs=["runs/direct-check.txt"], agent=state["researcher_agent"], memory_max="1G", queue=True,
    )
    extracted = submit_run(
        cfg, command=["python3", "-m", "es", "extract", "--check"], why="record direct extract",
        outputs=["runs/direct-extract.txt"], agent=state["researcher_agent"], memory_max="1G", queue=True,
    )
    with Store(cfg) as store:
        store.job_update(checked["id"], status="done", exit_code=0,
                         result_json=json.dumps({"ok": True, "rc": float("inf"), "outcome": float("nan")}))
        store.job_update(extracted["id"], status="done", exit_code=0,
                         result_json=json.dumps({"ok": True, "rc": 0}))

    summary = build_review(cfg, out)
    full = _full(cfg, summary)
    evidence = {item["job_id"]: item for item in full["validation"]["evidence"]}

    assert summary["counts"]["validation_evidence"] == 2
    assert summary["counts"]["explicit_proof_receipts"] == 0
    assert evidence[checked["id"]]["recorded_command"]["command"] == "check"
    assert evidence[extracted["id"]]["recorded_command"]["command"] == "extract"
    assert evidence[checked["id"]]["receipt"] == {"ok": True}
    assert all(item["explicit_proof_accepted"] is False for item in evidence.values())


def test_out_path_must_remain_in_configured_roots_and_cannot_traverse_symlink(cfg, project, tmp_path):
    out, _state = _run(cfg, project)
    with pytest.raises(CheckFailed, match="outside the project"):
        build_review(cfg, tmp_path / "elsewhere")

    link = project / "runs" / "linked"
    link.symlink_to(out, target_is_directory=True)
    with pytest.raises(UsageError, match="symlink"):
        build_review(cfg, link)

    sibling = project / "runs" / "sibling"
    sibling.mkdir()
    with pytest.raises(UsageError, match="ancestor"):
        build_review(cfg, out, artifact_root=sibling)
