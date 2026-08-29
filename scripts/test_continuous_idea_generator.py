#!/usr/bin/env python3
"""Regression tests for the bounded continuous idea generator."""

from __future__ import annotations

import json
import copy
from datetime import datetime, timezone
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from scripts import continuous_idea_generator as generator


class ContinuousIdeaGeneratorTests(unittest.TestCase):
    @staticmethod
    def authorization_args(**changes):
        values = {
            "approval_ref": "test-standing-approval",
            "generation_modes": list(generator.DEFAULT_GENERATION_MODES),
            "wall_minutes": 90,
            "max_calls_per_24h": 6,
            "minimum_cycle_interval_minutes": 30,
            "max_total_invocations": 100,
            "max_unreconciled_batches": 10,
            "max_unreconciled_seeds": 50,
            "max_consecutive_provider_stops": 2,
            "max_consecutive_zero_seed_batches": 2,
            "max_inline_bytes": 1024,
        }
        values.update(changes)
        return SimpleNamespace(**values)

    def test_provider_schema_binds_identity_and_snapshot(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "a" * 64}
        schema = generator.provider_schema("campaign-01", "context_rich", snapshot)
        properties = schema["properties"]
        self.assertEqual(properties["campaign_id"]["const"], "campaign-01")
        self.assertEqual(properties["generation_mode"]["const"], "context_rich")
        self.assertEqual(properties["snapshot"]["properties"]["path"]["const"], snapshot["path"])
        self.assertEqual(
            properties["terminal"]["enum"],
            ["SEED-BATCH-COMPLETE", "SEED-BATCH-NOVELTY-STOP"],
        )

    def test_provider_schema_removes_transport_unsupported_constraints(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "b" * 64}
        schema = generator.provider_schema("campaign-02", "failure_dual", snapshot)
        seed = schema["$defs"]["seed"]
        self.assertIn("title", seed["properties"])
        self.assertNotIn("maxLength", seed["properties"]["title"])
        self.assertNotIn("title", schema)
        self.assertNotIn("$schema", schema)

    def test_provider_schema_types_every_const_and_enum(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "e" * 64}
        schema = generator.provider_schema("campaign-03", "recombination", snapshot)

        def inspect(value) -> None:
            if isinstance(value, dict):
                if "const" in value or "enum" in value:
                    self.assertIn("type", value)
                for item in value.values():
                    inspect(item)
            elif isinstance(value, list):
                for item in value:
                    inspect(item)

        inspect(schema)

    def test_prompt_states_cross_field_model_invariants(self) -> None:
        snapshot = {"path": "runs/agents/test/snapshot.json", "sha256": "f" * 64}
        prompt = generator.make_prompt(
            "campaign-model-rule",
            "failure_dual",
            snapshot,
            generator.ROOT / "runs/agents/test-prompt",
        )
        self.assertIn("copy the exact same tier string", prompt)
        self.assertIn("set `bridge_ref` to null", prompt)
        self.assertIn("`verified_bridge` always requires", prompt)
        self.assertIn("unreconciled inbox batches", prompt)

    def test_stop_batch_validates_without_promoting_a_claim(self) -> None:
        packet = {
            "campaign_id": "campaign-stop",
            "generation_mode": "context_rich",
            "snapshot": {"path": "runs/agents/test/snapshot.json", "sha256": "c" * 64},
        }
        batch = generator.stop_batch(packet, "SEED-BATCH-PROVIDER-STOP")
        generator.campaign.validate_seed_batch(batch, authenticate=False)
        self.assertEqual(batch["seeds"], [])
        self.assertEqual(batch["claim_level"], "proposal")

    def test_provider_command_is_read_only_single_agent_sol_max(self) -> None:
        packet = {
            "provider": {"model": "gpt-5.6-sol", "reasoning_effort": "max"}
        }
        batch_dir = generator.ROOT / "runs/agents/test-command"
        argv = generator.provider_argv(packet, batch_dir)
        joined = " ".join(argv)
        self.assertIn("gpt-5.6-sol", argv)
        self.assertIn('model_reasoning_effort="max"', argv)
        self.assertIn('web_search="live"', argv)
        self.assertIn("agents.enabled=false", argv)
        self.assertIn("--sandbox read-only", joined)
        self.assertIn("--ephemeral", argv)
        self.assertIn("--skip-git-repo-check", argv)
        self.assertNotIn("danger-full-access", argv)

    def test_active_reserve_requires_exact_consumption_receipt(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            campaign_id = "reserve-test"
            batch_dir = service_dir / "batches" / campaign_id
            batch_dir.mkdir(parents=True)
            packet = {
                "campaign_id": campaign_id,
                "generation_mode": "context_rich",
                "snapshot": {"path": "runs/agents/test/snapshot.json", "sha256": "d" * 64},
            }
            seed_batch = generator.stop_batch(packet, "SEED-BATCH-NOVELTY-STOP")
            generator.atomic_json(batch_dir / "seed-batch.json", seed_batch)
            self.assertEqual(len(generator.active_reserve(service_dir)), 1)
            generator.atomic_json(
                service_dir / "consumed" / f"{campaign_id}.json",
                {"campaign_id": campaign_id},
            )
            self.assertEqual(generator.active_reserve(service_dir), [])

    def test_literal_seed_fingerprint_ignores_cosmetic_identity(self) -> None:
        batch = json.loads(
            (generator.ROOT / "templates/research-seed-batch.json").read_text(
                encoding="utf-8"
            )
        )
        first = batch["seeds"][0]
        renamed = copy.deepcopy(first)
        renamed["seed_id"] = "RENAMED"
        renamed["title"] = "Cosmetically renamed"
        renamed["lineage"]["parent_refs"] = ["UNRELATED-LABEL"]
        self.assertEqual(
            generator.seed_fingerprint(first), generator.seed_fingerprint(renamed)
        )

    def test_post_provider_filter_drops_prior_literal_core(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            prior = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            prior["campaign_id"] = "prior"
            prior_dir = service_dir / "batches" / "prior"
            prior_dir.mkdir(parents=True)
            generator.atomic_json(prior_dir / "seed-batch.json", prior)
            current = copy.deepcopy(prior)
            current["campaign_id"] = "current"
            current["seeds"][0]["seed_id"] = "RENAMED"
            current["seeds"][0]["title"] = "Renamed duplicate"
            filtered, report = generator.deduplicate_provider_batch(
                service_dir, current
            )
            self.assertEqual(filtered["terminal"], "SEED-BATCH-NOVELTY-STOP")
            self.assertEqual(filtered["seeds"], [])
            self.assertEqual(
                filtered["generation_metrics"]["literal_duplicates_removed"], 1
            )
            self.assertEqual(report["accepted_seed_count"], 0)

    def test_one_unreconciled_batch_does_not_block_v2_refill(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            batch = json.loads(
                (generator.ROOT / "templates/research-seed-batch.json").read_text(
                    encoding="utf-8"
                )
            )
            batch["campaign_id"] = "one-unreconciled"
            batch_dir = service_dir / "batches" / batch["campaign_id"]
            batch_dir.mkdir(parents=True)
            generator.atomic_json(batch_dir / "seed-batch.json", batch)
            authorization = {
                "limits": {
                    "max_unreconciled_batches": 10,
                    "max_unreconciled_seeds": 50,
                    "max_total_invocations": 100,
                    "max_calls_per_24h": 6,
                    "max_consecutive_provider_stops": 2,
                    "max_consecutive_zero_seed_batches": 2,
                    "minimum_cycle_interval_minutes": 30,
                }
            }
            gate = generator.generation_gate(service_dir, authorization)
            self.assertTrue(gate["ready"])
            self.assertEqual(gate["unreconciled_batches"], 1)
            self.assertEqual(gate["unreconciled_seeds"], 1)

    def test_rolling_call_cap_pauses_automatic_refill(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            for ordinal in range(2):
                batch_dir = service_dir / "batches" / f"cycle-{ordinal}"
                batch_dir.mkdir(parents=True)
                generator.atomic_json(
                    batch_dir / "packet.json",
                    {
                        "protocol": (
                            "continuous-idea-generator-v2"
                            if ordinal == 0
                            else generator.PROTOCOL_VERSION
                        ),
                        "campaign_id": f"cycle-{ordinal}",
                        "generation_mode": "context_rich",
                        "authority": {},
                    },
                )
                generator.atomic_json(
                    batch_dir / "attempt.json",
                    {"started_at": datetime.now(timezone.utc).isoformat()},
                )
            authorization = {
                "limits": {
                    "max_unreconciled_batches": 10,
                    "max_unreconciled_seeds": 50,
                    "max_total_invocations": 100,
                    "max_calls_per_24h": 2,
                    "max_consecutive_provider_stops": 2,
                    "max_consecutive_zero_seed_batches": 2,
                    "minimum_cycle_interval_minutes": 30,
                }
            }
            gate = generator.generation_gate(service_dir, authorization)
            self.assertFalse(gate["ready"])
            self.assertEqual(gate["reason"], "rolling-24h-call-cap")

    def test_two_provider_stops_open_circuit(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            for ordinal in range(2):
                batch_dir = service_dir / "batches" / f"stop-{ordinal}"
                batch_dir.mkdir(parents=True)
                generator.atomic_json(
                    batch_dir / "packet.json",
                    {
                        "protocol": generator.PROTOCOL_VERSION,
                        "campaign_id": f"stop-{ordinal}",
                        "generation_mode": "context_rich",
                        "authority": {},
                    },
                )
                stamp = datetime.now(timezone.utc).isoformat()
                generator.atomic_json(
                    batch_dir / "attempt.json", {"started_at": stamp}
                )
                generator.atomic_json(
                    batch_dir / "result-receipt.json",
                    {
                        "finished_at": stamp,
                        "terminal": "SEED-BATCH-PROVIDER-STOP",
                        "seed_count": 0,
                    },
                )
            authorization = {
                "limits": {
                    "max_unreconciled_batches": 10,
                    "max_unreconciled_seeds": 50,
                    "max_total_invocations": 100,
                    "max_calls_per_24h": 6,
                    "max_consecutive_provider_stops": 2,
                    "max_consecutive_zero_seed_batches": 2,
                    "minimum_cycle_interval_minutes": 30,
                }
            }
            gate = generator.generation_gate(service_dir, authorization)
            self.assertFalse(gate["ready"])
            self.assertEqual(gate["reason"], "provider-stop-circuit-open")

    def test_frozen_cycle_is_bound_to_standing_authorization(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            args = self.authorization_args()
            authorization = generator.make_standing_authorization(service_dir, args)
            authorization_path = generator.authorization_file_path(
                service_dir, authorization
            )
            generator.atomic_json(authorization_path, authorization)

            def fake_build(output_dir: Path, _max_inline_bytes: int):
                output_dir.mkdir(parents=True, exist_ok=True)
                for name, value in (
                    ("manifest.json", {}),
                    ("context.md", "context\n"),
                    ("lean-declarations.md", "declarations\n"),
                    ("prior-idea-registry.json", {}),
                    ("packet-summary.json", {"manifest_aggregate_sha256": "1" * 64}),
                ):
                    path = output_dir / name
                    if isinstance(value, dict):
                        generator.atomic_json(path, value)
                    else:
                        path.write_text(value, encoding="utf-8")
                return {"manifest_aggregate_sha256": "1" * 64}

            with mock.patch.object(
                generator.build_sol_idea_packet, "build_packet", side_effect=fake_build
            ):
                frozen = generator.freeze_campaign_packet(
                    service_dir,
                    "standing-cycle-test",
                    "context_rich",
                    authorization_path,
                    authorization,
                )
            packet_path = generator.ROOT / frozen["packet"]["path"]
            packet = generator.verify_packet(packet_path)
            self.assertEqual(
                packet["standing_authorization"]["sha256"],
                generator.sha256(authorization_path),
            )
            self.assertFalse(packet["authority"]["may_retry_attempted_packet"])

    def test_write_once_refuses_immutable_drift(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            path = Path(raw) / "receipt.json"
            generator.write_once(path, {"value": 1})
            generator.write_once(path, {"value": 1})
            with self.assertRaises(generator.ServiceError):
                generator.write_once(path, {"value": 2})

    def test_standing_authorization_binds_helpers_and_schema(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            authorization = generator.make_standing_authorization(
                service_dir, self.authorization_args()
            )
            authorization_path = generator.authorization_file_path(
                service_dir, authorization
            )
            generator.atomic_json(authorization_path, authorization)
            generator.verify_standing_authorization(
                authorization_path, service_dir=service_dir
            )
            tampered = copy.deepcopy(authorization)
            tampered["supporting_implementation"][0]["sha256"] = "0" * 64
            tampered_path = service_dir / "authorizations" / "tampered.json"
            generator.atomic_json(tampered_path, tampered)
            with self.assertRaisesRegex(generator.ServiceError, "helper or schema"):
                generator.verify_standing_authorization(
                    tampered_path, service_dir=service_dir
                )

    def test_standing_authorization_cannot_weaken_call_limits(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            with self.assertRaisesRegex(generator.ServiceError, "wall_minutes"):
                generator.make_standing_authorization(
                    service_dir, self.authorization_args(wall_minutes=91)
                )
            with self.assertRaisesRegex(generator.ServiceError, "at least 30"):
                generator.make_standing_authorization(
                    service_dir,
                    self.authorization_args(minimum_cycle_interval_minutes=29),
                )

    def test_active_pointer_rotation_preserves_prior_authorization(self) -> None:
        generator.RUNS_ROOT.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=generator.RUNS_ROOT) as raw:
            service_dir = Path(raw)
            first = generator.make_standing_authorization(
                service_dir, self.authorization_args()
            )
            first_path = generator.authorization_file_path(service_dir, first)
            generator.write_once(first_path, first)
            first_hash = generator.sha256(first_path)
            pointer_path = generator.active_authorization_pointer_path(service_dir)
            generator.atomic_json(
                pointer_path,
                {
                    "schema_version": 1,
                    "protocol": generator.PROTOCOL_VERSION,
                    "activated_at": "first",
                    "authorization": generator.file_receipt(first_path),
                },
            )
            self.assertEqual(
                generator.active_standing_authorization(service_dir)[0], first_path
            )

            second = copy.deepcopy(first)
            second["created_at"] = "second"
            second_path = generator.authorization_file_path(service_dir, second)
            generator.write_once(second_path, second)
            generator.atomic_json(
                pointer_path,
                {
                    "schema_version": 1,
                    "protocol": generator.PROTOCOL_VERSION,
                    "activated_at": "second",
                    "authorization": generator.file_receipt(second_path),
                },
            )
            self.assertNotEqual(first_path, second_path)
            self.assertEqual(generator.sha256(first_path), first_hash)
            self.assertEqual(
                generator.active_standing_authorization(service_dir)[0], second_path
            )

    def test_process_identity_rejects_pid_reuse_shape(self) -> None:
        identity = generator.process_identity(os.getpid())
        self.assertIsNotNone(identity)
        assert identity is not None
        self.assertTrue(generator.process_identity_matches(identity))
        reused = dict(identity)
        reused["start_ticks"] += 1
        self.assertFalse(generator.process_identity_matches(reused))

    def test_start_rejects_stale_daemon_under_standing_authorization(self) -> None:
        args = SimpleNamespace(
            service_dir=Path("runs/agents/test-service"),
            authorization=Path(
                "runs/agents/test-service/authorizations/current.json"
            ),
            authorization_sha256="a" * 64,
        )
        service_dir = generator.ROOT / args.service_dir
        authorization_path = generator.ROOT / args.authorization
        with (
            mock.patch.object(generator, "service_directory", return_value=service_dir),
            mock.patch.object(
                generator, "packet_path_argument", return_value=authorization_path
            ),
            mock.patch.object(generator, "sha256", return_value="a" * 64),
            mock.patch.object(
                generator,
                "active_standing_authorization",
                return_value=(authorization_path, {}),
            ),
            mock.patch.object(
                generator,
                "launch_daemon",
                side_effect=generator.ServiceError("stale implementation"),
            ),
        ):
            with self.assertRaisesRegex(generator.ServiceError, "stale"):
                generator.command_start(args)

    def test_stop_disables_failed_unit_without_live_daemon_receipt(self) -> None:
        args = SimpleNamespace(
            service_dir=Path("runs/agents/test-service"), reason="test-stop"
        )
        service_dir = generator.ROOT / args.service_dir
        completed = SimpleNamespace(returncode=0)
        with (
            mock.patch.object(generator, "service_directory", return_value=service_dir),
            mock.patch.object(generator, "daemon_receipt", return_value=None),
            mock.patch.object(generator.subprocess, "run", return_value=completed) as run,
            mock.patch("builtins.print"),
        ):
            self.assertEqual(generator.command_stop(args), 0)
        self.assertEqual(
            run.call_args.args[0],
            [
                "systemctl",
                "--user",
                "disable",
                "--now",
                generator.SYSTEMD_UNIT_NAME,
            ],
        )

    def test_service_directory_cannot_escape_run_root(self) -> None:
        with self.assertRaises(generator.ServiceError):
            generator.service_directory(Path("/tmp/not-a-project-service"))


if __name__ == "__main__":
    unittest.main()
