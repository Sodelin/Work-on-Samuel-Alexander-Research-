Deterministic one-generation sharing graph: proof checkpoint

Owned source: real/PedigreeBlockGraph.lean.
Shared model: real/PedigreeBlockModel.lean, maintained by the coordinating lane.

There are n+1 labeled children and B Boolean block choices per child. Share
requires distinct children and an equal choice in at least one block.
Connected means reflexive-transitive reachability between every pair.
Bad is the shared anchored event: every child's vector is the first vector
or its complement, and a complementary vector actually occurs.

The main theorem is:

    PedigreeBlock.not_connected_iff_bad
      (hB : 0 < B) (x : Config n B) :
      (not Connected x) iff Bad x

The positive-block assumption matters. It ensures that a code and its
complement are distinct, so the anchored event describes two nonempty
classes. In particular the theorem includes a singleton family (n=0);
that family is connected and its Bad event is empty.

The proof first identifies nonedges between distinct children with
complementary codes. For an unreachable pair a,b, their codes are
complementary. A third code outside that pair would share with a and b and
produce a two-edge path, a contradiction. Every code therefore has one of
the two types; reanchoring at child zero yields Bad. Conversely, in Bad,
each edge preserves which type its endpoints have, so every path does too.
The represented complementary child cannot be reached from child zero.

The additional pathwise result uses restrictBlocks hBD x to retain the first
B coordinates of a D-block configuration, where B<=D. Every old sharing
edge is witnessed by the same embedded block index in the longer code.
Induction on reflexive-transitive paths proves reachable_of_restrict.
Consequently connected_of_restrict shows that once a family is connected,
adding observed blocks cannot destroy its connectivity. These results do
not assume random or independent inheritance.

The final printed acceptance endpoints are:

- PedigreeBlock.not_share_iff_complement
- PedigreeBlock.not_connected_iff_bad
- PedigreeBlock.reachable_of_restrict
- PedigreeBlock.connected_of_restrict

All of these are general proofs, with no enumeration of a fixed child/block
case. Probability counting and the observation-symbol interpretation are
owned by their separate modules. This graph module makes no direct claim
about the continuous Wong ARG law, multigeneration REC-GEN, or Alexander
specieslike classification.

Run only the requested import closure through the coordinated lock:

```powershell
$env:WONG_COMPILER_LOCK = 'C:\Users\Owner\Documents\Codex\2026-09-27\wong-alexander\.local-build\wong-continuation\compiler.lock'
python -X utf8 research\wong\continuation-2026-09-27\check.py PedigreeBlockGraph
```

The verifier uses pinned Lean 4.33.1 and mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Successful development evidence is
preserved in this directory's RESULT.json, module log/row and import-closure
receipt. Development checks do not replace the coordinator's final combined
clean-commit audit. The frozen earlier checkout is not edited by this lane.

Development verification passed on the second run (13.411 seconds for the
graph module, two project modules in its import closure). The first run's
three elaboration errors and their diagnostics are preserved in attempt-1.
All four acceptance endpoints are checked; both prefix-path endpoints are
axiom-free, and the remaining endpoints use only standard allowed axioms.
RESULT.json pins this frozen source snapshot. No further source edits are
pending in this lane.
