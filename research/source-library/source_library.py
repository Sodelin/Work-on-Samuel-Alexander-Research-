#!/usr/bin/env python3
"""Local source metadata and page-text library. Python standard library only."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sqlite3
import sys
import uuid
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlparse

SCHEMA_VERSION = 1
READ_STATES = {"metadata_only", "full_text_unread", "partially_read", "read"}
AVAILABILITY = {"full_text_available", "missing", "title_only"}
CLAIM_STATES = {"unreviewed", "source_checked", "disputed"}
PROOF_STATES = {"unreviewed", "not_formalized", "partial", "checked"}


class IntakeError(ValueError):
    pass


def now():
    return datetime.now(timezone.utc).isoformat()


def identifier(kind, value):
    kind = str(kind).strip().casefold()
    value = str(value).strip()
    if kind == "doi":
        value = re.sub(r"^(?:https?://(?:dx\.)?doi\.org/|doi:\s*)", "", value, flags=re.I)
    elif kind == "arxiv":
        value = re.sub(r"^https?://arxiv\.org/(?:abs|pdf)/", "", value, flags=re.I)
        value = re.sub(r"\.pdf$", "", value, flags=re.I)
    if not kind or not value:
        raise IntakeError("Identifiers require nonempty kind and value.")
    return kind, value.casefold()


def web_url(value):
    if not isinstance(value, str):
        return False
    p = urlparse(value)
    return p.scheme in {"https", "http"} and bool(p.netloc) and not p.username and not p.password


def fresh(prefix):
    return prefix + "_" + uuid.uuid4().hex[:16]


def load_json(path):
    with Path(path).open(encoding="utf-8-sig") as f:
        return json.load(f)


def connect(path):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(path, timeout=10)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA foreign_keys=ON")
    db.executescript("""
    CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT NOT NULL);
    CREATE TABLE IF NOT EXISTS sources(
        source_id TEXT PRIMARY KEY, metadata TEXT NOT NULL, created_at TEXT NOT NULL);
    CREATE TABLE IF NOT EXISTS identifiers(
        kind TEXT NOT NULL, value TEXT NOT NULL, version_key TEXT NOT NULL,
        source_id TEXT NOT NULL REFERENCES sources(source_id),
        UNIQUE(kind,value,version_key));
    CREATE TABLE IF NOT EXISTS artifacts(
        artifact_id TEXT PRIMARY KEY, source_id TEXT NOT NULL REFERENCES sources(source_id),
        source_sha256 TEXT UNIQUE, local_path TEXT, hash_status TEXT NOT NULL);
    CREATE TABLE IF NOT EXISTS intake_aliases(
        intake_id TEXT PRIMARY KEY, artifact_id TEXT NOT NULL REFERENCES artifacts(artifact_id));
    CREATE TABLE IF NOT EXISTS pages(
        artifact_id TEXT NOT NULL REFERENCES artifacts(artifact_id),
        page_number INTEGER NOT NULL CHECK(page_number>0),
        unit_type TEXT NOT NULL, label TEXT NOT NULL, locator TEXT NOT NULL,
        text TEXT NOT NULL, text_sha256 TEXT NOT NULL, extraction_status TEXT NOT NULL,
        added_at TEXT NOT NULL, UNIQUE(artifact_id,page_number,text_sha256));
    CREATE TABLE IF NOT EXISTS observations(
        source_id TEXT NOT NULL REFERENCES sources(source_id),
        artifact_id TEXT NOT NULL REFERENCES artifacts(artifact_id),
        observed_at TEXT NOT NULL, intake_metadata TEXT NOT NULL);
    """)
    row = db.execute("SELECT value FROM settings WHERE key='schema_version'").fetchone()
    if row and int(row[0]) != SCHEMA_VERSION:
        raise IntakeError("Unsupported database schema version; no migration attempted.")
    db.execute("INSERT OR IGNORE INTO settings VALUES('schema_version',?)", (str(SCHEMA_VERSION),))
    db.commit()
    return db


def validate_record(raw):
    if not isinstance(raw, dict):
        raise IntakeError("Each source must be an object.")
    r = dict(raw)
    if r.get("title") is not None and not isinstance(r["title"], str):
        raise IntakeError("title must be an explicitly supplied string or null.")
    if r.get("title") and not r.get("title_provenance"):
        raise IntakeError("A supplied title requires title_provenance; filenames are not title evidence.")
    if r.get("kind", "pdf") not in {"pdf", "transcript", "title_entry", "other"}:
        raise IntakeError("Unknown source kind.")
    for key, choices in [("read_status", READ_STATES), ("availability", AVAILABILITY)]:
        if key in r and r[key] not in choices:
            raise IntakeError("Invalid " + key)
    v = r.get("verification", {})
    if v.get("claim_status", "unreviewed") not in CLAIM_STATES:
        raise IntakeError("Invalid verification.claim_status")
    if v.get("proof_status", "unreviewed") not in PROOF_STATES:
        raise IntakeError("Invalid verification.proof_status")
    if v.get("proof_status") in {"partial", "checked"} and not v.get("scope"):
        raise IntakeError("Proof status partial/checked requires an explicit scope.")
    if v.get("proof_status") == "checked" and not v.get("evidence"):
        raise IntakeError("Checked proof status requires evidence; ingest does not verify a proof.")
    for u in r.get("authoritative_urls", []):
        if not web_url(u):
            raise IntakeError("authoritative_urls must contain credential-free HTTP(S) URLs.")
    for note in r.get("public_notes", []):
        if not isinstance(note, dict) or not web_url(note.get("url")):
            raise IntakeError("public_notes require an explicit public HTTP(S) URL.")
    pub = r.get("observed_publication", {})
    if not isinstance(pub, dict):
        raise IntakeError("observed_publication must be an object.")
    version = str(pub.get("version") or "unknown").strip().casefold()
    ids = [identifier(k, x) for k, val in r.get("identifiers", {}).items()
           for x in (val if isinstance(val, list) else [val])]
    pages = r.get("pages", [])
    if not isinstance(pages, list):
        raise IntakeError("pages must be a list.")
    for page in pages:
        n = page.get("page_number")
        if not isinstance(n, int) or isinstance(n, bool) or n < 1:
            raise IntakeError("Each page_number must be a positive one-based integer.")
        if not isinstance(page.get("text"), str):
            raise IntakeError("Each page requires text, including an explicit empty string if blank.")
        if page.get("unit_type", "page") not in {"page", "segment"}:
            raise IntakeError("unit_type must be page or segment.")
        if page.get("unit_type") == "segment" and not page.get("locator"):
            raise IntakeError("Transcript segments require a line/time locator; no page is invented.")
        if page.get("extraction_status", "unreviewed") not in {"unreviewed", "visually_verified"}:
            raise IntakeError("Unknown extraction_status.")
    supplied = r.get("source_sha256")
    if supplied is not None:
        supplied = str(supplied).casefold()
        if not re.fullmatch(r"[0-9a-f]{64}", supplied):
            raise IntakeError("source_sha256 must be a full 64-character hexadecimal SHA-256.")
    local = r.get("local_path")
    status = "declared" if supplied else "not_available"
    if local and Path(local).is_file():
        with Path(local).open("rb") as handle:
            h = hashlib.file_digest(handle, "sha256").hexdigest()
        if supplied and h != supplied:
            raise IntakeError("Supplied source hash differs from actual file: " + str(local))
        supplied, status = h, "verified_local_bytes"
    if not (supplied or ids or r.get("intake_id")):
        raise IntakeError("Supply a source hash, identifier or stable intake_id for deduplication.")
    return r, ids, version, supplied, status


def initial_metadata(r):
    return {
        "kind": r.get("kind", "pdf"), "title": r.get("title"),
        "title_provenance": r.get("title_provenance"),
        "authors": r.get("authors", []), "rights": r.get("rights", "unconfirmed"),
        "authoritative_urls": r.get("authoritative_urls", []),
        "observed_publication": r.get("observed_publication", {"date": None, "version": None}),
        "provenance": r.get("provenance", []),
        "read_status": r.get("read_status", "full_text_unread" if r.get("pages") else "metadata_only"),
        "availability": r.get("availability", "full_text_available" if r.get("pages") else
                              ("title_only" if r.get("kind") == "title_entry" else "missing")),
        "verification": r.get("verification", {"claim_status": "unreviewed", "proof_status": "unreviewed", "evidence": []}),
        "public_notes": r.get("public_notes", []),
    }


def merge_metadata(old, raw, warnings):
    incoming = initial_metadata(raw)
    # A reading owner's explicit first-page metadata can resolve a PDF-metadata title.
    if raw.get("title") and (raw.get("title_provenance") or {}).get("kind") == "first_page_text_extraction" and (old.get("title_provenance") or {}).get("kind") == "pdf_metadata":
        old["title"], old["title_provenance"] = raw["title"], raw["title_provenance"]
    for key, value in incoming.items():
        if key not in raw:
            continue
        if key in {"authoritative_urls", "provenance", "public_notes"}:
            for item in value:
                if item not in old.setdefault(key, []):
                    old[key].append(item)
        elif key == "read_status" and old.get(key) in {"partially_read", "read"} and value in {"metadata_only", "full_text_unread"}:
            pass
        elif key == "verification" and old.get(key, {}).get("proof_status") in {"partial", "checked"} and value.get("proof_status") == "unreviewed":
            pass
        elif key == "observed_publication" and old.get(key):
            for field, observed in value.items():
                if observed is None:
                    continue
                if old[key].get(field) in (None, "", "publication_date_unconfirmed"):
                    old[key][field] = observed
                elif old[key][field] != observed and field != "observed_at":
                    old.setdefault("metadata_conflicts", []).append({"field": key + "." + field, "observed_value": observed})
        elif key in {"title", "title_provenance"} and old.get(key) and value and old[key] != value:
            old.setdefault("metadata_conflicts", []).append({"field": key, "observed_value": value})
            warnings.append("Conflicting " + key + " retained as a metadata observation; original display value preserved.")
        elif key in {"authors", "rights"} and old.get(key) and value in (None, [], "unconfirmed"):
            pass
        elif key == "kind" and old.get(key) == "title_entry" and value == "other":
            pass
        elif value is not None:
            old[key] = value
    return old


def ingest(db, payload):
    records = payload.get("sources") if isinstance(payload, dict) and "sources" in payload else [payload]
    if not isinstance(records, list):
        raise IntakeError("sources must be a list.")
    if isinstance(payload, dict) and payload.get("schema_version", 1) != 1:
        raise IntakeError("Unsupported intake schema_version.")
    validated = [validate_record(r) for r in records]
    result = []
    db.execute("BEGIN IMMEDIATE")
    try:
        for r, ids, version, source_hash, hash_status in validated:
            warnings, candidates = [], set()
            artifact = db.execute("SELECT * FROM artifacts WHERE source_sha256=?", (source_hash,)).fetchone() if source_hash else None
            if artifact:
                candidates.add(artifact["source_id"])
            alias = db.execute("SELECT a.* FROM intake_aliases i JOIN artifacts a USING(artifact_id) WHERE intake_id=?",
                               (r.get("intake_id"),)).fetchone()
            if alias:
                candidates.add(alias["source_id"])
                if source_hash and alias["source_sha256"] and source_hash != alias["source_sha256"]:
                    raise IntakeError("intake_id was reused for different bytes; use a new artifact intake_id.")
                artifact = artifact or alias
            for kind, value in ids:
                candidates.update(x[0] for x in db.execute(
                    "SELECT source_id FROM identifiers WHERE kind=? AND value=? AND version_key=?",
                    (kind, value, version)))
            if len(candidates) > 1:
                raise IntakeError("Conflicting hash/identifier identities; refusing to silently merge existing sources.")
            sid = next(iter(candidates)) if candidates else fresh("src")
            old = db.execute("SELECT metadata FROM sources WHERE source_id=?", (sid,)).fetchone()
            metadata = merge_metadata(json.loads(old[0]), r, warnings) if old else initial_metadata(r)
            if old:
                db.execute("UPDATE sources SET metadata=? WHERE source_id=?", (json.dumps(metadata), sid))
            else:
                db.execute("INSERT INTO sources VALUES(?,?,?)", (sid, json.dumps(metadata), now()))
            for kind, value in ids:
                db.execute("INSERT OR IGNORE INTO identifiers VALUES(?,?,?,?)", (kind, value, version, sid))
            if not artifact:
                aid = fresh("art")
                db.execute("INSERT INTO artifacts VALUES(?,?,?,?,?)",
                           (aid, sid, source_hash, r.get("local_path"), hash_status))
            else:
                aid = artifact["artifact_id"]
                if hash_status == "verified_local_bytes":
                    db.execute("UPDATE artifacts SET hash_status=?,local_path=?,source_sha256=COALESCE(source_sha256,?) WHERE artifact_id=?",
                               (hash_status, r.get("local_path"), source_hash, aid))
            if r.get("intake_id"):
                db.execute("INSERT OR IGNORE INTO intake_aliases VALUES(?,?)", (r["intake_id"], aid))
            added = 0
            for page in r.get("pages", []):
                n, text = page["page_number"], page["text"]
                th = hashlib.sha256(text.encode("utf-8")).hexdigest()
                different = db.execute("SELECT 1 FROM pages WHERE artifact_id=? AND page_number=? AND text_sha256<>?",
                                       (aid, n, th)).fetchone()
                if different:
                    warnings.append("Page " + str(n) + " has an additional extraction variant; both preserved.")
                unit = page.get("unit_type", "page")
                label = str(page.get("label", n))
                locator = page.get("locator") or ("PDF page " + str(n) + ("; printed " + label if label != str(n) else ""))
                cur = db.execute("INSERT OR IGNORE INTO pages VALUES(?,?,?,?,?,?,?,?,?)",
                                 (aid, n, unit, label, str(locator), text, th,
                                  page.get("extraction_status", "unreviewed"), now()))
                added += cur.rowcount
            observation = {k: v for k, v in r.items() if k != "pages"}
            db.execute("INSERT INTO observations VALUES(?,?,?,?)", (sid, aid, now(), json.dumps(observation)))
            result.append({"source_id": sid, "artifact_id": aid, "intake_id": r.get("intake_id"),
                           "new_source": not bool(old), "pages_added": added, "warnings": warnings})
        if isinstance(payload, dict) and "discovery_anchors" in payload:
            anchors = payload["discovery_anchors"]
            if not isinstance(anchors, list) or any(not isinstance(a, dict) or not web_url(a.get("url")) for a in anchors):
                raise IntakeError("discovery_anchors require HTTP(S) URLs.")
            db.execute("INSERT OR REPLACE INTO settings VALUES('discovery_anchors',?)", (json.dumps(anchors),))
        db.commit()
    except Exception:
        db.rollback()
        raise
    return result


def catalog(db):
    out = []
    for source in db.execute("SELECT * FROM sources ORDER BY created_at,source_id"):
        sid, meta = source["source_id"], json.loads(source["metadata"])
        record = {"source_id": sid, "created_at": source["created_at"], **meta}
        record["title"] = record.get("title") or None
        record["title_display"] = record["title"] or "[Title unconfirmed]"
        record["identifiers"] = [dict(x) for x in db.execute(
            "SELECT kind,value,version_key FROM identifiers WHERE source_id=? ORDER BY kind,value", (sid,))]
        artifacts = []
        for art in db.execute("SELECT * FROM artifacts WHERE source_id=? ORDER BY artifact_id", (sid,)):
            a = {k: art[k] for k in ["artifact_id", "source_sha256", "hash_status"]}
            a["intake_ids"] = [x[0] for x in db.execute("SELECT intake_id FROM intake_aliases WHERE artifact_id=?", (art["artifact_id"],))]
            a["text_unit_count"] = db.execute("SELECT count(DISTINCT page_number) FROM pages WHERE artifact_id=?", (art["artifact_id"],)).fetchone()[0]
            a["text_variant_count"] = db.execute("SELECT count(*) FROM pages WHERE artifact_id=?", (art["artifact_id"],)).fetchone()[0]
            a["original_file_status"] = "present" if art["local_path"] and Path(art["local_path"]).is_file() else ("missing" if art["local_path"] else "not_specified")
            artifacts.append(a)
        record["artifacts"] = artifacts
        record["has_searchable_text"] = any(a["text_unit_count"] for a in artifacts)
        record["verification_is_imported_metadata"] = True
        # Export provenance methods and authoritative links, never local file paths.
        record["provenance"] = [{k: v for k, v in x.items()
                                 if k in {"method", "observed_at"} or (k in {"source", "source_url"} and web_url(v))}
                                for x in record.get("provenance", []) if isinstance(x, dict)]
        record.pop("metadata_conflicts", None)
        record["title_provenance"] = public_fields(record.get("title_provenance"),
            {"kind", "locator", "status", "observed_at"})
        record["observed_publication"] = public_fields(record.get("observed_publication"),
            {"date", "year", "version", "observed_at", "status"})
        verification = record.get("verification", {})
        record["verification"] = public_fields(verification,
            {"claim_status", "proof_status", "scope"})
        record["verification"]["evidence"] = [
            {"url": e["url"], "title": e.get("title", "Evidence")}
            for e in verification.get("evidence", [])
            if isinstance(e, dict) and web_url(e.get("url"))]
        record["verification"]["local_evidence_count"] = len(verification.get("evidence", [])) - len(record["verification"]["evidence"])
        out.append(record)
    anchor_row = db.execute("SELECT value FROM settings WHERE key='discovery_anchors'").fetchone()
    anchors = [{"url": a["url"], "status": a.get("status", "unconfirmed")} for a in json.loads(anchor_row[0])] if anchor_row else []
    return {"schema_version": SCHEMA_VERSION, "exported_at": now(), "sources": out, "discovery_anchors": anchors,
            "notice": "Metadata catalog only. Full corpus stays local. Reading/proof statuses are intake declarations, not independently verified by this CLI."}


def public_fields(value, allowed):
    return {k: v for k, v in (value or {}).items()
            if k in allowed or (k in {"url", "source_url"} and web_url(v))}


def snippet(text, start, size):
    left = max(0, start - size // 3)
    if left:
        left = min(len(text), left + len(text[left:].split(" ", 1)[0]) + 1)
    body = text[left:left + size - 2]
    return (("…" if left else "") + body + ("…" if left + len(body) < len(text) else ""))[:size]


def search(db, query, phrase=False, limit=10, snippet_chars=240, source_id=None):
    if not query.strip() or not 1 <= limit <= 100 or not 40 <= snippet_chars <= 1000:
        raise IntakeError("Search requires a query, limit 1-100, and snippet_chars 40-1000.")
    terms = [query.strip()] if phrase else query.split()
    patterns = [re.compile(r"\s+".join(re.escape(x) for x in term.split()), re.I) for term in terms]
    sql = """SELECT p.*,a.source_id,a.source_sha256,s.metadata,
             (SELECT count(*) FROM pages v WHERE v.artifact_id=p.artifact_id AND v.page_number=p.page_number) AS variants
             FROM pages p JOIN artifacts a USING(artifact_id) JOIN sources s USING(source_id)"""
    params = ()
    if source_id:
        sql += " WHERE (a.source_id=? OR a.artifact_id IN (SELECT artifact_id FROM intake_aliases WHERE intake_id=?))"
        params = (source_id, source_id)
    sql += " ORDER BY a.source_id,p.artifact_id,p.page_number,p.added_at"
    hits = []
    for row in db.execute(sql, params):
        flat = re.sub(r"\s+", " ", row["text"]).strip()
        matches = [p.search(flat) for p in patterns]
        if not all(matches):
            continue
        meta = json.loads(row["metadata"])
        hits.append({"source_id": row["source_id"], "artifact_id": row["artifact_id"],
                     "intake_ids": [x[0] for x in db.execute("SELECT intake_id FROM intake_aliases WHERE artifact_id=?", (row["artifact_id"],))],
                     "source_sha256": row["source_sha256"], "title": meta.get("title"),
                     "page_number": row["page_number"], "unit_type": row["unit_type"],
                     "label": row["label"], "locator": row["locator"],
                     "text_variant": row["text_sha256"], "variants_at_locator": row["variants"],
                     "extraction_status": row["extraction_status"], "read_status": meta["read_status"],
                     "snippet": snippet(flat, min(m.start() for m in matches), snippet_chars),
                     "authoritative_urls": meta.get("authoritative_urls", [])})
        if len(hits) >= limit:
            break
    return {"query": query, "mode": "phrase" if phrase else "all_keywords",
            "limit": limit, "hits": hits}


def markdown_catalog(data):
    def esc(s):
        return str(s if s is not None else "unknown").replace("|", "\\|").replace("\n", " ")
    lines = ["# Local research source catalog", "", data["notice"], "",
             "| Source ID | Explicit title | Publication / version | Reading | Availability | Claim / proof metadata | Searchable units |",
             "|---|---|---|---|---|---|---|"]
    for r in data["sources"]:
        pub, ver = r.get("observed_publication", {}), r.get("verification", {})
        lines.append("| " + " | ".join(map(esc, [
            r["source_id"], r["title_display"],
            str(pub.get("date") or "date unknown") + " / " + str(pub.get("version") or "version unknown"),
            r["read_status"], r["availability"],
            ver.get("claim_status", "unreviewed") + " / " + ver.get("proof_status", "unreviewed"),
            sum(a["text_unit_count"] for a in r["artifacts"])])) + " |")
    for r in data["sources"]:
        lines += ["", "## " + r["source_id"] + " — " + esc(r["title_display"]), ""]
        for url in r["authoritative_urls"]:
            lines.append("- [Authoritative source](" + url.replace(")", "%29") + ")")
        for note in r.get("public_notes", []):
            lines.append("- [" + esc(note.get("title", "Our note")).replace("]", "\\]") + "](" + note["url"].replace(")", "%29") + ")")
        if not r["has_searchable_text"]:
            lines.append("- **No page text ingested; full text is missing or unread.**")
        lines.append("- Declared proof scope: " + esc(r.get("verification", {}).get("scope", "none")))
    if data.get("discovery_anchors"):
        lines += ["", "## Discovery anchors", "", "These links do not establish a complete bibliography.", ""]
        for anchor in data["discovery_anchors"]:
            lines.append("- [Discovery source](" + anchor["url"] + "): " + esc(anchor["status"]))
    return "\n".join(lines) + "\n"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", type=Path, default=Path(__file__).with_name("corpus.sqlite3"))
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("init")
    ing = sub.add_parser("ingest"); ing.add_argument("intake", type=Path)
    adapter = sub.add_parser("import-intake"); adapter.add_argument("manifest", type=Path)
    adapter.add_argument("--pages-dir", type=Path)
    sub.add_parser("list")
    q = sub.add_parser("search"); q.add_argument("query"); q.add_argument("--phrase", action="store_true")
    q.add_argument("--limit", type=int, default=10); q.add_argument("--snippet-chars", type=int, default=240); q.add_argument("--source")
    ex = sub.add_parser("export"); ex.add_argument("output_dir", type=Path)
    args = parser.parse_args(argv)
    try:
        with connect(args.db) as db:
            if args.command == "init":
                result = {"database": str(args.db.resolve()), "schema_version": SCHEMA_VERSION}
            elif args.command == "ingest":
                result = {"ingested": ingest(db, load_json(args.intake))}
            elif args.command == "import-intake":
                from intake_adapter import adapt_intake
                payload, receipt = adapt_intake(args.manifest, args.pages_dir)
                result = {"ingested": ingest(db, payload), "intake_receipt": receipt}
            elif args.command == "list":
                result = catalog(db)
            elif args.command == "search":
                result = search(db, args.query, args.phrase, args.limit, args.snippet_chars, args.source)
            else:
                data = catalog(db); args.output_dir.mkdir(parents=True, exist_ok=True)
                jp, mp = args.output_dir / "catalog.json", args.output_dir / "CATALOG.md"
                jp.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
                mp.write_text(markdown_catalog(data), encoding="utf-8")
                result = {"json": str(jp), "markdown": str(mp), "source_count": len(data["sources"]), "corpus_text_exported": False}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (IntakeError, OSError, sqlite3.Error, json.JSONDecodeError) as exc:
        print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.modules.setdefault("source_library", sys.modules[__name__])
    raise SystemExit(main())

