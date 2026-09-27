# Deterministic marked Big-ARG recorder

Implementation: `real/WongMarkedRecorder.lean`. Status: compiled PASS with Lean 4.33.1 and the pinned Mathlib; 28 selected declarations passed the explicit axiom audit. The arbitrary-history construction and controls are checked. Final combined probability construction and exact integration commit verification remain the coordinator's separate obligations.

## Source-to-statement correspondence

| Source obligation | Construction or checked theorem |
|---|---|
| Appendix B selects extant lineages, not endpoint pairs | `RawState.active`, `Mark`; stable natural lineage ID keys are independent of child and parent vertices |
| Recombinant event consumes one lineage and produces two | `split`, `split_preserves_valid`, `split_frontier_count` |
| Interior breakpoint partitions the complete genome | `Cut`, `splitIntervals`, `advance_valid`; new intervals are `[lo,cut)` and `[cut,hi)` independent of the consumed slot's interval |
| Common ancestor consumes two distinct lineages | `merge`, `merge_preserves_valid`, `merge_frontier_count`; no distinct-child assumption |
| Rootward slots resolve to edges | `rawRecord`, `old_completed_record_preserved`; completion retains identity and interval |
| Every created genome has exactly one inheritance slot at every coordinate | `Valid.coverage`, `completed_frontier_exact_slot`; uniqueness is at stable lineage-ID level, with completed/frontier ID sets proved disjoint |
| Finite graph recording | `Trace`, `finite_prefix_valid`, `trace_event_vertices`, `recorded_prefix_toGARG`, exact topology and locus equivalences |
| DAG and unique parent at a locus | strict fresh parent IDs imply `projected_path_strict`; `projected_unique_parent_at` follows from the slot theorem |
| Stopped clock dates | `dated_prefix_chronology_bounded`, requiring only positive and increasing actual event dates |
| Stop at one lineage, with no extra event | `count_one_stop`, `start_one_no_event`, `step_reaching_one_is_merge`, `merge_terminal_root` |
| Equal event endpoints retain raw crossover boundary | `raw_records_injective`, `rawEncodingEquiv`, `reunion_encoded_records`, `reunion_raw_decode` |

## Shared-endpoint decoder issue

The old `WongEventDecoding.Normalized` predicate excludes a crossover whose eventual two parent vertices coincide. That exclusion does not follow from the Big-ARG sampler: the two new lineages may be immediately selected together for merger. The new decoder is defined on raw interval-record sets, not local-parent semantics. Its checked injectivity proof recovers the strict interior boundary from the raw interval endpoints, then recovers the ordered parent identities from local inheritance. It needs no distinct-parent condition.

The recorder control creates that exact history, with counts `2,3,2,1`. Lineages 2 and 3 have the same parent 3 and child 2 after immediate reunion but retain complementary intervals. Different cut positions give different actual raw recorder states while their local-parent semantics agree. Thus raw record preservation repairs the decoder domain; merging intervals or retaining only local-parent semantics necessarily loses the cut.

## Scope boundaries

The raw state has explicit data and a separate validity predicate. Initialization and actual updates prove the predicate; graph validity is not an assumed output field. Proof-indexed marks reject malformed input by lacking a constructor; this is not an executable untrusted-file validator. The decoder is a classical inverse on its explicit encoding range, not a file parser.

The coordinate type is any linear order, with strict interior cuts. A probability law must separately choose and justify its coordinate regime, prove that its marks inhabit these types, and show that the random finite stopped fold is measurable and exists almost surely. Deterministic finite induction does not discharge these stochastic obligations or complete B04/B05. No biological species classification follows from this recorder.

## Verification command

From the isolated repository root, with the coordinator's serial compiler grant:

```powershell
python -X utf8 research\wong\continuation-2026-09-27\check.py WongMarkedRecorder
```

The verifier uses Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, one Lean process and a 4096 MB limit, rebuilding project imports into the isolated private object directory. The successful module/import-closure receipts, full compiler warnings, and 28-declaration axiom log are retained in this directory. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the selected dependency audits. No `sorry`, `admit`, added axiom, `sorryAx`, or native-decision trust extension is used. The source was compiled in the working tree based at `01db8c4cbb82000950ff7d3e7252b5438416c7c3`; its final committed integration must be verified separately.

## Admitted artifact hashes

- Source SHA256: `1dcec9e5522f03adf21a308bd31a64a5f10a445b567bc72701916009972bdfea`.
- Lean object SHA256: `4f527e28f5fa6f597b220e53d0ab6823c33d5ea88013b140f98ac45c2b4dc663`.
- Full compiler log SHA256: `d3d9ffc66b570c3908bd1ff27fedd1ff5ea1017bde358270aa30909bae6726c9`.
- Axiom log SHA256: `cac67b14b197f319895531b0907a15cd65edbc06abd9a3e2e62ae50cebe6c11a`.

`VERIFICATION.json` is the compact receipt. `module-receipt.json` contains the imported project-object hashes. `import-closure-receipt.json` retains the 10-module requested closure and baseline commit. `compiler.log` retains all warnings: these are unused-variable/simp/tactic suggestions, not proof errors.

No deterministic theorem remains failed in the admitted file. The remaining work is the separately owned actual random-mark law, measurable random stopped fold, count-and-time pushforward identity, and combined exact-commit/source audit. The shortest next route is to construct `Mark lo hi s` from supported finite-set/pair/cut innovations, use `applyMark_valid` and the two count-update theorems inductively along the count path, and use `finite_prefix_valid` with `recorded_prefix_toGARG` at its first count-one index. The source-faithful time proof should use `dated_prefix_chronology_bounded`, which makes no assertion about the stopped clock after its last actual event.
