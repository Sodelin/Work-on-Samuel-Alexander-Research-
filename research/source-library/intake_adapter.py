"""Adapter for the research reading task's source-provenance v1.0 manifest."""
import hashlib
import json
import re
from pathlib import Path


def file_hash(path):
    with Path(path).open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def adapt_intake(manifest_path, pages_dir=None):
    # Import lazily so the library remains independently importable in tests.
    from source_library import IntakeError, identifier, load_json, web_url
    manifest_path = Path(manifest_path)
    manifest = load_json(manifest_path)
    if str(manifest.get("schemaVersion")) != "1.0":
        raise IntakeError("Expected source-provenance schemaVersion 1.0.")
    pages_dir = Path(pages_dir) if pages_dir else manifest_path.parent / "extracted"
    records, receipt = [], []
    for item in manifest["files"]:
        sid = item["sourceId"]
        original = str(item.get("sha256Original") or "").lower()
        staged_hash = str(item.get("sha256Staged") or original).lower()
        if original and staged_hash != original:
            raise IntakeError("Staged/original hash disagreement: " + sid)
        bib = item.get("bibliographic") or {}
        pdfmeta = (item.get("pdf") or {}).get("metadata") or {}
        title = bib.get("title") or pdfmeta.get("/Title") or None
        ids = {}
        doi = bib.get("DOI") or bib.get("doi") or pdfmeta.get("/DOI") or pdfmeta.get("/doi")
        arxiv = bib.get("arXivId") or pdfmeta.get("/arXivID")
        if doi:
            ids["doi"] = identifier("doi", doi)[1]
        if arxiv:
            ids["arxiv"] = identifier("arxiv", arxiv)[1]
        version = bib.get("arXivVersion") or bib.get("version")
        if not version and arxiv:
            match = re.search(r"v(\d+)$", ids["arxiv"])
            version = "v" + match[1] if match else None
        urls = [u for u in [bib.get("officialUrl")] if web_url(u)]
        if doi:
            urls.append("https://doi.org/" + ids["doi"])
        if arxiv:
            urls.append("https://arxiv.org/abs/" + ids["arxiv"])
        observed = manifest.get("lastUpdatedUtc") or manifest.get("intakeTimeUtc")
        derivative = next((d for d in item.get("derivatives", [])
                           if str(d.get("path", "")).endswith(".pages.jsonl")), {})
        sidecar = Path(item.get("textSidecar") or derivative.get("path") or pages_dir / (sid + ".pages.jsonl"))
        pages, sidecar_hash = [], None
        if sidecar.is_file():
            sidecar_hash = file_hash(sidecar)
            expected = item.get("textSidecarSha256") or derivative.get("sha256")
            if expected and sidecar_hash != str(expected).lower():
                raise IntakeError("Sidecar hash mismatch: " + sid)
            if derivative.get("parentSha256") and str(derivative["parentSha256"]).lower() != original:
                raise IntakeError("Derivative parent hash mismatch: " + sid)
            with sidecar.open(encoding="utf-8-sig") as handle:
                for line_number, line in enumerate(handle, 1):
                    if not line.strip():
                        continue
                    row = json.loads(line)
                    if row.get("sourceId") != sid or str(row.get("originalSha256", "")).lower() != original:
                        raise IntakeError("Sidecar row identity mismatch: " + sid + " line " + str(line_number))
                    kind = row.get("locatorType", "pdf-page")
                    if kind in {"line-range", "text-line"}:
                        first = row.get("startLine", row.get("lineStart"))
                        last = row.get("endLine", row.get("lineEnd"))
                        if not isinstance(first, int) or not isinstance(last, int) or first < 1 or last < first:
                            raise IntakeError("Invalid transcript line range: " + sid)
                        locator = "line " + str(first) if first == last else "lines " + str(first) + "–" + str(last)
                        page = {"page_number": first, "unit_type": "segment", "label": locator, "locator": locator}
                    elif kind == "pdf-page":
                        n, label = row.get("pageNumber"), row.get("pageLabel")
                        locator = "PDF page " + str(n) + ("; printed " + str(label) if label is not None else "")
                        page = {"page_number": n, "unit_type": "page", "label": str(label) if label is not None else str(n), "locator": locator}
                    else:
                        raise IntakeError("Unsupported locatorType: " + str(kind))
                    page.update(text=row["text"], extraction_status="visually_verified" if row.get("verificationStatus") == "visually_verified" else "unreviewed")
                    pages.append(page)
        kind = "pdf" if item.get("pdf") or "pdf" in item.get("detectedType", "").lower() else "transcript" if item.get("textLineCount") else "other"
        local = item.get("stagedPath") or item.get("sourcePath")
        available = bool(local and Path(local).is_file())
        record = {
            "intake_id": sid, "kind": kind, "title": title,
            "title_provenance": {"kind": "bibliographic_intake" if bib.get("title") else "pdf_metadata", "status": "intake_declared" if bib.get("title") else "unconfirmed"} if title else None,
            "authors": bib.get("authors") or ([pdfmeta["/Author"]] if pdfmeta.get("/Author") else []),
            "rights": item.get("rights") or item.get("rightsStatus") or pdfmeta.get("/License") or "unconfirmed",
            "identifiers": ids, "source_sha256": original or None, "local_path": local,
            "authoritative_urls": list(dict.fromkeys(urls)),
            "observed_publication": {"date": bib.get("date"), "year": bib.get("year"), "version": version, "observed_at": observed,
                                     "status": "intake_declared" if bib else "publication_date_unconfirmed"},
            "provenance": [{"method": "preserved user-source intake", "source": str(manifest_path), "observed_at": observed},
                           {"method": "page/line sidecar; extraction unverified", "source": str(sidecar), "observed_at": observed}],
            "read_status": item.get("readStatus", "full_text_unread" if available else "metadata_only"),
            "availability": "full_text_available" if available and kind != "other" else "title_only" if available else "missing",
            "verification": item.get("verification") or {"claim_status": "unreviewed", "proof_status": "unreviewed", "scope": "No proof verification imported by this intake adapter", "evidence": []},
            "pages": pages,
        }
        records.append(record)
        receipt.append({"intake_id": sid, "sidecar_sha256": sidecar_hash, "text_units": len(pages),
                        "text_status": "searchable_extraction_unverified" if pages else "no_text_ingested", "title_status": "explicit_metadata" if title else "unconfirmed"})
    return {"schema_version": 1, "sources": records}, {"manifest_sha256": file_hash(manifest_path), "sources": receipt}
