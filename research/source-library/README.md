# Local research source library

This is a working, local, standard-library Python tool for finding passages in the user's preserved research documents. It uses the reading task's existing extraction, with exact source hashes and PDF page or transcript line addresses. It is a local source resource; it does not connect to an Anna's Archive API.

## Public snapshot and local corpus

This repository includes the tool and metadata catalog. The working SQLite corpus and full-text extraction are local and are not included. A fresh checkout must import its own authorized source manifest before text search returns those documents. Reading statuses are the intake snapshot; later source-specific reviews in the open-problem program record the passages actually examined.

## Current usable collection

The first completed import contains **20 PDFs with 710 PDF pages**, **one transcript with 582 line segments**, and **two BBS commentary entries whose full text has not been read**. One of those commentary entries is linked to the preserved screenshot. The metadata catalog therefore has **23 source entries**. These counts describe the recorded import, not future uploads.

The texts are searchable extractions. The library has not visually checked the extraction or verified the papers' mathematics. Bibliographic values from PDF metadata are marked unconfirmed; unknown titles remain `[Title unconfirmed]`. No title is inferred from a filename, and a PDF creation timestamp is not treated as its publication date.

The source-reading task owns interpretation. Its manifest is at `../friston-ancestry-feasibility/work/source-provenance.json`; its extraction sidecars are under that task's `work/extracted/` directory. Original source files remain there. The local SQLite database stores a searchable copy of their page text.

## Use

Run these commands from this directory with Python 3.11 or later. No packages or network access are required.

```powershell
python -X utf8 source_library.py list
python -X utf8 source_library.py search "self-reference" --limit 5
python -X utf8 source_library.py search "free energy" --phrase --limit 5
python -X utf8 source_library.py search "open question" --phrase --source doc-8b3940d8ac53
python -X utf8 source_library.py search "reasoning" --source doc-c899ab08a3cd --limit 3
```

The `--source` filter accepts either the library's source ID or the reading task's `doc-...` ID. `doc-8b3940d8ac53` is the preserved `rsos.261059.pdf` artifact; the filename is an artifact label, not an inferred title. Search output includes:

- Stable library source and artifact IDs, plus intake IDs and the full source SHA-256.
- Exact PDF page or transcript line locator. PDF page numbers are one-based; a printed page label is shown separately when the sidecar supplies one.
- A bounded snippet, normally at most 240 characters, and extraction/read status.
- A text-variant hash when different extractions exist for the same page.

Default search requires every keyword to occur somewhere in the same page or segment, using case-insensitive substring matching. `--phrase` requires the phrase in order and tolerates whitespace/line breaks. It does not stem words, repair OCR, rank relevance, expand synonyms, or match across page boundaries. Results follow source/artifact/page order; the result limit is not a total match count. An empty result is a search result, not evidence that an idea is absent from the literature.

## Update from the reading task

Once new sidecars are ready, run:

```powershell
python -X utf8 source_library.py import-intake ../friston-ancestry-feasibility/work/source-provenance.json
python -X utf8 source_library.py ingest discovery-intake.json
python -X utf8 source_library.py ingest reader-metadata-intake.json
python -X utf8 source_library.py export public
```

The adapter accepts the manifest's explicit `textSidecar` path, its derivative path, or the conventional `extracted/<sourceId>.pages.jsonl` path. It checks the actual source bytes, supplied derivative hashes, and each row's source ID and original hash. It supports `pdf-page`, `text-line` with `lineStart/lineEnd`, and `line-range` with `startLine/endLine`.

Reimporting identical bytes and page text adds no duplicate pages. DOI/identifier normalization matches the same explicit version while distinct supplied versions stay separate. Different byte artifacts retain their own pagination even when they share a source identity. Contradictory identities fail the transaction. A changed extraction is preserved as an additional variant, not silently substituted. Old reading and checked-proof declarations are not downgraded by an unreviewed extraction import.

The database file contains the stable library IDs: preserve it if those IDs have already been cited. Intake IDs, source hashes, and page locators allow the extraction to be independently located if a new database is built.

## Shareable artifacts and local-only material

- `public/CATALOG.md` and `public/catalog.json` contain metadata, source links, hashes, reading/verification statuses, and counts. They omit page text, local source paths, and private proof-evidence paths.
- `reader-metadata-intake.json` records the reading owner's eight supplied first-page titles/identifiers, with publisher confirmation pending and the version conflict preserved.
- `discovery-intake.json` records coordinator-supplied publisher metadata for the BBS entries and institutional discovery anchors. The historical author-selected bibliography is explicitly **not** represented as a complete or current bibliography.
- `corpus.sqlite3`, `local-ingestion-receipt.json`, and `local-search-demonstration.json` remain local. The search demonstration contains short source excerpts; it is excluded from version control with the corpus.

Review metadata before public posting. The tool provides a metadata-only export rather than a bulk source-text export. Rights/license entries are imported declarations; missing license information remains unconfirmed.

## Reading, claims, and proofs are different records

`read_status` can be `metadata_only`, `full_text_unread`, `partially_read`, or `read`. A searchable extraction normally remains `full_text_unread` until the reading owner records otherwise.

Claim status can be `unreviewed`, `source_checked`, or `disputed`. Proof status can be `unreviewed`, `not_formalized`, `partial`, or `checked`. Unknown proof status defaults to `unreviewed`; it does not assert that no formalization exists. A `partial` or `checked` proof declaration requires a stated scope; `checked` also requires evidence. The CLI validates those fields but does not run Lean or certify the declaration. Private evidence remains local; public evidence URLs may appear in the catalog.

## Native intake format

`ingest` accepts one source record or `{"schema_version": 1, "sources": [...]}`. A minimal record with missing full text is:

```json
{
  "intake_id": "my-source-v1",
  "kind": "title_entry",
  "title": null,
  "identifiers": {"doi": "10.example/explicitly-supplied-id"},
  "observed_publication": {"date": null, "version": null},
  "availability": "missing",
  "read_status": "metadata_only",
  "verification": {"claim_status": "unreviewed", "proof_status": "unreviewed", "evidence": []},
  "pages": []
}
```

An explicit title requires `title_provenance`. Pages use `page_number`, `text`, and optional `label`, `locator`, `extraction_status`; transcript units additionally use `unit_type: "segment"` and an explicit line/time locator. `local_path` plus `source_sha256` verifies the original bytes. Optional metadata includes `authors`, `rights`, `authoritative_urls`, `provenance`, and `public_notes` with explicit HTTP(S) links.

## Verification

```powershell
python -X utf8 -m unittest -v test_source_library.py
```

The bounded tests cover byte deduplication, normalized identifiers and versions, exact page/line citations, phrase matching and snippet limits, preservation of extraction variants, transaction rollback on conflicting identities, metadata export boundaries, and rejection of mismatched source/sidecar identity. `VERIFICATION.json` records the real import and test result. This is software verification of the local indexing tool, not a mathematical proof review of the imported papers.
