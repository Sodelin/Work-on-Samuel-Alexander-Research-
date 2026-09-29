"""Behavioral tests for identity, citation, corpus privacy, and intake integrity."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from source_library import IntakeError, catalog, connect, ingest, search
from intake_adapter import adapt_intake


class LibraryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.db = connect(self.root / "test.sqlite3")

    def tearDown(self):
        self.db.close()
        self.temp.cleanup()

    def record(self, tag="a", **extra):
        record = {"intake_id": tag, "source_sha256": hashlib.sha256(tag.encode()).hexdigest(),
                  "pages": [{"page_number": 3, "label": "ii", "text": "A Markov\nblanket example. " * 20}]}
        record.update(extra)
        return record

    def test_identical_bytes_are_idempotent_and_aliases_preserved(self):
        r = self.record()
        first = ingest(self.db, r)[0]
        second = ingest(self.db, {**r, "intake_id": "duplicate"})[0]
        self.assertEqual(first["source_id"], second["source_id"])
        self.assertEqual(second["pages_added"], 0)
        hit = search(self.db, "Markov blanket", phrase=True)["hits"][0]
        self.assertEqual(hit["intake_ids"], ["a", "duplicate"])

    def test_identifier_normalization_keeps_artifacts_and_versions(self):
        r1 = self.record("a", identifiers={"doi": "HTTPS://DOI.ORG/10.1234/Example"}, observed_publication={"version": "v1"})
        r2 = self.record("b", identifiers={"doi": "doi:10.1234/example"}, observed_publication={"version": "v1"})
        r3 = self.record("c", identifiers={"doi": "10.1234/example"}, observed_publication={"version": "v2"})
        first, second, third = ingest(self.db, {"sources": [r1, r2, r3]})
        self.assertEqual(first["source_id"], second["source_id"])
        self.assertNotEqual(first["artifact_id"], second["artifact_id"])
        self.assertNotEqual(first["source_id"], third["source_id"])

    def test_phrase_search_returns_exact_page_and_bounded_snippet(self):
        sid = ingest(self.db, self.record())[0]["source_id"]
        hit = search(self.db, "Markov blanket", phrase=True, snippet_chars=80, source_id=sid)["hits"][0]
        self.assertEqual(hit["source_id"], sid)
        self.assertEqual(hit["page_number"], 3)
        self.assertEqual(hit["locator"], "PDF page 3; printed ii")
        self.assertLessEqual(len(hit["snippet"]), 80)
        self.assertIn("Markov blanket", hit["snippet"])
        self.assertEqual(search(self.db, "not present", phrase=True)["hits"], [])

    def test_conflicting_page_extractions_are_preserved(self):
        ingest(self.db, self.record())
        ingest(self.db, self.record(pages=[{"page_number": 3, "text": "Markov blanket corrected extraction."}]))
        hits = search(self.db, "Markov blanket", phrase=True)["hits"]
        self.assertEqual(len(hits), 2)
        self.assertTrue(all(x["variants_at_locator"] == 2 for x in hits))

    def test_conflicting_source_identities_roll_back_batch(self):
        ingest(self.db, self.record("a", identifiers={"doi": "10.1234/a"}))
        ingest(self.db, self.record("b", identifiers={"doi": "10.1234/b"}))
        with self.assertRaises(IntakeError):
            ingest(self.db, {"sources": [self.record("c"), self.record("a", identifiers={"doi": "10.1234/b"})]})
        self.assertEqual(len(catalog(self.db)["sources"]), 2)

    def test_export_omits_text_local_paths_and_private_evidence(self):
        private = str(self.root / "private-proof.lean")
        r = self.record(title="Explicit title", title_provenance={"kind": "publisher", "local_path": private},
                        provenance=[{"method": "local intake", "source": private}],
                        verification={"proof_status": "checked", "scope": "one named lemma", "evidence": [{"path": private}]})
        ingest(self.db, r)
        exported = json.dumps(catalog(self.db))
        self.assertNotIn("Markov", exported)
        self.assertNotIn(str(self.root), exported)
        self.assertNotIn("private-proof", exported)
        self.assertIn('"local_evidence_count": 1', exported)

    def test_adapter_transcript_locator_and_parent_hash_check(self):
        source = self.root / "transcript.txt"
        source.write_text("actual text", encoding="utf-8")
        sha = hashlib.sha256(source.read_bytes()).hexdigest()
        pages = self.root / "source.pages.jsonl"
        row = {"sourceId": "doc-test", "originalSha256": sha, "locatorType": "text-line",
               "lineStart": 17, "lineEnd": 19, "text": "Bayesian reasoning", "verificationStatus": "extracted-unverified"}
        pages.write_text(json.dumps(row) + "\n", encoding="utf-8")
        manifest = self.root / "source-provenance.json"
        manifest.write_text(json.dumps({"schemaVersion": "1.0", "files": [{"sourceId": "doc-test", "sha256Original": sha,
            "stagedPath": str(source), "textLineCount": 19, "sourceFileName": "DO NOT INFER TITLE.txt", "textSidecar": str(pages)}]}), encoding="utf-8")
        payload, _ = adapt_intake(manifest)
        self.assertIsNone(payload["sources"][0]["title"])
        ingest(self.db, payload)
        hit = search(self.db, "reasoning")["hits"][0]
        self.assertEqual(hit["locator"], "lines 17–19")
        self.assertEqual(hit["unit_type"], "segment")
        row["originalSha256"] = "0" * 64
        pages.write_text(json.dumps(row), encoding="utf-8")
        with self.assertRaises(IntakeError):
            adapt_intake(manifest)

    def test_actual_local_bytes_checked_before_ingestion(self):
        local = self.root / "source.pdf"
        local.write_bytes(b"document")
        with self.assertRaises(IntakeError):
            ingest(self.db, self.record(local_path=str(local)))
        self.assertEqual(catalog(self.db)["sources"], [])


if __name__ == "__main__":
    unittest.main()
