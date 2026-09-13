"""Additive operational schema; none of these records establishes a Lean theorem."""

SCHEMA = """
CREATE TABLE IF NOT EXISTS automation_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS artifacts (
 id TEXT PRIMARY KEY, path TEXT NOT NULL, bytes INTEGER NOT NULL, kind TEXT NOT NULL, created_at REAL NOT NULL);
CREATE TABLE IF NOT EXISTS operations (
 id TEXT PRIMARY KEY, operation_key TEXT NOT NULL UNIQUE, kind TEXT NOT NULL, agent TEXT NOT NULL,
 root TEXT NOT NULL, node TEXT, window_id TEXT, spec_json TEXT NOT NULL, status TEXT NOT NULL,
 created_at REAL NOT NULL, updated_at REAL NOT NULL, result_json TEXT, cancel_requested INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS operation_stages (
 operation_id TEXT NOT NULL, ordinal INTEGER NOT NULL, name TEXT NOT NULL,
 status TEXT NOT NULL, attempt INTEGER NOT NULL DEFAULT 0, job_id TEXT,
 input_hash TEXT NOT NULL, result_json TEXT, started_at REAL, finished_at REAL,
 PRIMARY KEY(operation_id, ordinal), UNIQUE(operation_id, name));
CREATE TABLE IF NOT EXISTS deliveries (
 id TEXT PRIMARY KEY, operation_id TEXT NOT NULL, agent TEXT NOT NULL, payload_json TEXT NOT NULL,
 status TEXT NOT NULL, created_at REAL NOT NULL, acknowledged_at REAL,
 consumer TEXT, lease_until REAL, attempts INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS usage_records (
 provider TEXT NOT NULL, session_id TEXT NOT NULL, response_id TEXT NOT NULL, at TEXT NOT NULL,
 input_tokens INTEGER NOT NULL, cached_input_tokens INTEGER NOT NULL,
 output_tokens INTEGER NOT NULL, reasoning_output_tokens INTEGER NOT NULL,
 model TEXT, effort TEXT, window_id TEXT, operation_id TEXT, association TEXT NOT NULL,
 source_path TEXT NOT NULL, source_line INTEGER NOT NULL,
 PRIMARY KEY(provider, session_id, response_id));
CREATE TABLE IF NOT EXISTS usage_imports (
 source_path TEXT PRIMARY KEY, bytes INTEGER NOT NULL, records INTEGER NOT NULL,
 report_json TEXT NOT NULL, imported_at REAL NOT NULL);
CREATE TABLE IF NOT EXISTS research_windows (
 id TEXT PRIMARY KEY, agent TEXT NOT NULL, label TEXT NOT NULL, cohort TEXT, arm TEXT,
 status TEXT NOT NULL, started_at TEXT NOT NULL, ended_at TEXT,
 output_budget INTEGER, accepted_results INTEGER, metadata_json TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS resource_leases (
 id TEXT PRIMARY KEY, job_id TEXT, pid INTEGER, process_start TEXT, memory_gib REAL NOT NULL,
 lock_key TEXT, created_at REAL NOT NULL);
CREATE TABLE IF NOT EXISTS tool_metrics (
 id TEXT PRIMARY KEY, at REAL NOT NULL, agent TEXT NOT NULL, command TEXT NOT NULL,
 full_bytes INTEGER NOT NULL, returned_bytes INTEGER NOT NULL, operation_id TEXT, window_id TEXT);
CREATE INDEX IF NOT EXISTS operation_state ON operations(status);
CREATE INDEX IF NOT EXISTS stage_job ON operation_stages(job_id);
CREATE INDEX IF NOT EXISTS delivery_pending ON deliveries(agent,status);
CREATE INDEX IF NOT EXISTS usage_window ON usage_records(window_id);
INSERT OR IGNORE INTO automation_meta(key,value) VALUES ('schema_version','1');
"""
