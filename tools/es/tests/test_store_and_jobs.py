import time

from es.store import Store


def test_claims_expire(cfg):
    with Store(cfg) as st:
        st.claim("TCore.a", "agent1", ttl_hours=0.0000001, note="n")
        assert "TCore.a" in st.claims()
    time.sleep(0.01)
    with Store(cfg) as st:
        assert "TCore.a" not in st.claims()
        outcomes = [a["outcome"] for a in st.attempts("TCore.a")]
        assert "expired" in outcomes


def test_claim_release_records_attempt(cfg):
    with Store(cfg) as st:
        st.claim("TCore.b", "agent1", ttl_hours=1)
        assert st.release("TCore.b", "agent1", outcome="abandoned")
        assert not st.release("TCore.b", "agent1")
        assert [a["outcome"] for a in st.attempts("TCore.b")] == ["abandoned"]


def test_conclude_attempt_records_exactly_one_claimed_or_standalone_attempt(cfg):
    with Store(cfg) as st:
        st.claim("TCore.claimed", "agent1", ttl_hours=1)
        assert st.conclude_attempt("TCore.claimed", "agent1", "closed", note="es close")
        assert not st.conclude_attempt("TCore.standalone", "agent1", "retired", note="obsolete")
        claimed = [dict(row) for row in st.attempts("TCore.claimed")]
        standalone = [dict(row) for row in st.attempts("TCore.standalone")]
        assert [(row["outcome"], row["note"]) for row in claimed] == [("closed", "es close")]
        assert [(row["outcome"], row["note"]) for row in standalone] == [("retired", "obsolete")]

        st.claim("TCore.checked", "agent1", ttl_hours=1)
        st.record_attempt("TCore.checked", "agent1", "closed", note="es check")
        assert st.conclude_attempt("TCore.checked", "agent1", "closed", note="es close")
        checked = [dict(row) for row in st.attempts("TCore.checked")]
        assert [(row["outcome"], row["note"]) for row in checked] == [
            ("closed", "es check"), ("closed", "es close")]


def test_two_agents_see_each_other(cfg):
    with Store(cfg) as st1:
        st1.claim("TCore.c", "agent1", ttl_hours=1)
    with Store(cfg) as st2:
        assert st2.claims()["TCore.c"]["agent"] == "agent1"


def test_job_state_machine(cfg):
    from es.jobs import run_job, submit

    job = submit(cfg, kind="build", node=None, argv=["doctor"], agent="tester", queue=True)
    with Store(cfg) as st:
        assert st.job(job["id"])["status"] == "queued"
    done = run_job(cfg, job["id"])
    assert done["status"] in ("done", "failed") and done["exit_code"] is not None
    with Store(cfg) as st:
        assert st.job(job["id"][:8])["id"] == job["id"]


def test_search_index(cfg):
    with Store(cfg) as st:
        st.search_rebuild([{"name": "TCore.strong_five_free", "module": "TCore.X", "kind": "theorem", "doc": "a strong five-free support window", "type_pp": "True"},
                           {"name": "TCore.other", "module": "TCore.Y", "kind": "def", "doc": "unrelated", "type_pp": "Nat"}], "s1")
        hits = st.search("strong five-free support")
        assert hits and hits[0]["name"] == "TCore.strong_five_free"
        assert st.search_stamp() == "s1"


def test_cache_roundtrip(cfg):
    with Store(cfg) as st:
        st.cache_put("t1", {"a": 1}, [{"b": 2}])
        assert st.cache_get("t1") == ({"a": 1}, [{"b": 2}])
        assert st.cache_get("nope") is None


def test_targeted_cache_entries_do_not_evict_full_ones(cfg):
    with Store(cfg) as st:
        st.cache_put("full1", {"a": 1}, [])
        for i in range(12):
            st.cache_put(f"t{i}+Mod{i}", {"t": i}, [])
        assert st.cache_get("full1") == ({"a": 1}, [])
        assert st.cache_get("t0+Mod0") == ({"t": 0}, [])


def test_open_is_lock_free_once_schema_is_current(cfg):
    """Steady-state opens take no write lock: WAL mode is on, the schema stamp is current, and an
    open (with a read) succeeds while another connection holds an uncommitted write transaction."""
    import sqlite3
    from es.store import schema_stamp
    with Store(cfg) as st:
        assert st.conn.execute("PRAGMA journal_mode").fetchone()[0].lower() == "wal"
        assert st.conn.execute("PRAGMA user_version").fetchone()[0] == schema_stamp()
        st.log("first", None, "a")
    writer = sqlite3.connect(cfg.db_path, timeout=1)
    try:
        writer.execute("BEGIN IMMEDIATE")
        writer.execute("INSERT INTO events(at, kind) VALUES (0, 'held')")
        reader = Store(cfg)
        reader.conn.execute("PRAGMA busy_timeout = 200")
        try:
            assert not reader.readonly
            kinds = [r["kind"] for r in reader.events_since(0)]
            assert "log" in kinds and "held" not in kinds   # sees committed rows, not the open write
        finally:
            reader.conn.close()
    finally:
        writer.rollback()
        writer.close()


def test_expired_claim_purge_writes_only_when_something_expired(cfg):
    with Store(cfg) as st:
        assert st.purge_expired_claims() == 0
        assert not st.conn.in_transaction
