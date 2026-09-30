# All-level NANUQ: focused quality improvement

Decision: retain six total taxa as the proved structural witness bound. The
all-level result already allows arbitrary finite level and arbitrary finite
taxon count. A witness bound measures the size of a local proof obligation;
reducing it does not enlarge that network class.

## Strongest currently supported statement

The audited computer-assisted argument establishes original-NANUQ circularity
for every finite binary semi-directed LSA, outer-labeled planar, galled network
with at least four taxa, including networks with multiple blobs, at every
finite reticulation level. The separate all-level representation, finite, and
composition audits support this statement. No all-level displayed-split support
equality, canonical identification, statistical consistency, external peer
review, or historical priority is certified by this conclusion.

The canonical theta local theorem is fully checked in Lean, including exact
displayed-edge support. The complete raw-source all-level theorem is not yet
formalized. These are different verification scopes.

## Why four is not a justified replacement

An anchor coefficient uses two anchors and four boundary endpoints. Its four
entries can therefore involve six distinct taxon labels. A four-point test of
the full metric is different from recomputing a metric separately on a
four-taxon restricted network.

A new focused exact check gives a concrete obstruction for the stronger
parameter-family certificate. For scores

    (c,s,a,o) = (1,1,1/2,1),

all 117 saved coefficients on three and four taxa pass. An actual saved
five-label paired-tip tree fails:

    expanded labels: [0,0,1,2,3,4]
    tree on physical positions: [0, [[[1,2],3], [4,5]]]
    anchors: (0,1); boundary gaps: (2,4)
    alpha = M(2,4)+M(3,0)-M(2,0)-M(3,4)
          = 1+1-1-2 = -1 = 2(a-c).

Both global copy choices were checked independently using graph distances;
their distinct quartet codes are [5,5,1,1,1]. This is an actual paired-tip
representation witness, not an arbitrary collection of incompatible quartets.
The receipt and reproducer are FOUR-TAXON-OBSTRUCTION.json and
check_four_taxon_obstruction.py.

Consequently, four TOTAL taxa cannot certify the full parameterized
anchor-positivity criterion. This does not show failure at original NANUQ
scores, prove six is optimal rather than five, or rule out a specialized
four-taxon proof using additional structural information. This witness has
four single-copy taxa and one duplicated taxon; total labels and ordinary
leaves must not be conflated.

## New Lean certificate for the exact parameter domain

AllLevelParameterDomain.lean now proves, over the real numbers, that the
sixteen independently enumerated normalized coefficient inequalities hold
exactly when

    s = o = 1,  1/2 <= a <= 1,  0 <= c <= a.

Here c is the singleton-cherry score, s the singleton-separated score, a the
two-topology adjacent score, and o the two-topology opposite score. The
shared-anchor entry remains normalized to 1.

The same Lean module proves that the ten row types found on at most four taxa
give only the weaker box

    s = o = 1,  0 <= a <= 1,  0 <= c <= 1.

It formally checks two accepted-by-four/rejected-by-full points, including the
five-label witness above. Five taxa already produce every one of the sixteen
row types; six introduce no additional inequality type in the exhaustive
certificate. That is a reduction of the algebraic inequality basis, not a
proof that every six-label structural witness compresses to five labels.

Lean exit status is zero, and the printed axiom dependencies are only
propext, Classical.choice, and Quot.sound. This verifies the exact real-algebra
step. It does not by itself verify the external enumeration or the source
graph representation; those remain at their separately recorded audited
computer-assisted verification level.

## A scope repair that matters

The parameter domain supplies the local bloblet/weighted anchor theorem. It
cannot be transferred to multiple blobs using the original anchor identity
unchanged when c > 0. If a bridge resolves pq|xy, the generalized global anchor
entry is 2c, while the relevant local branching-blob entries vanish. A global
parameter-family theorem needs a correction. Original NANUQ has c=0 and is
unaffected by this obstruction.

## Recommended next effort

Keep the safe six-label structural bound. The highest-value next formal step
is the all-level paired-tip representation and preservation of the distinct
quartet sets, followed by the already audited general composition argument.
This replaces per-level casework with one reusable theorem. Treat all-level
exact support as a separate prospective strengthening. Do not advertise a
minimal witness bound or transfer the whole parameter family globally without
the missing argument.

The earlier 94-module canonical checkpoint is independently rebuilding from
its frozen source snapshot. This report and the new parameter-domain module
are a separate focused addition; completion of that background rebuild is not
being asserted here.
