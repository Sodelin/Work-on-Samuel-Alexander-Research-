# Independent review of the diploid pairing counterexample

**Review status:** the proposed counterexample is mathematically sound under the
explicit observation and reproduction contract below. The exact finite checks
passed on 2026-09-27. This note supplies an all-generation proof, not a Lean
verification receipt. No novelty claim is made. The reviewer changed only this
file and did not run a compiler.

## The precise claim worth preserving

One complete, infinite **unpaired genome-copy transmission graph**, with the
same copy identities, dates and genomic interval on every edge, admits two
diploid owner maps whose exact edge-image pedigrees have opposite whole-graph
IAP and inspecies status. Both pedigrees are weakly connected, have four
organisms per generation, two distinct parents per nonfounder, two children per
organism, and owner fibres of size exactly two. They can agree on owner
metadata through any prescribed finite generation. They can also share
consistent binary organism-sex annotations on every genome copy.

The omitted information is **which two genome copies belong to one organism**.
This is not a claim that an observation already containing all individual
assignments fails to determine the pedigree. Given the entire owner map and
the exact edge-image premise, the pedigree is determined mathematically.
Nor is this a theorem that two stochastic genetic observation laws coincide.

## Construction and exact target definitions

Let genomic vertices be `(t,i)`, where `t` is a natural-number generation and
`0 <= i < 8`. The only edges are `(t,i) -> (t+1,i)`, each carrying the same
nonempty interval, for example `[0,1)`. Thus the graph consists of eight
infinite transmission lanes. At each generation, pair lanes using one of:

| Index | M0: P blocks | M1: Q blocks | M2: R blocks |
| --- | --- | --- | --- |
| 0 | {0,1} | {1,2} | {1,2} |
| 1 | {2,3} | {3,4} | {3,0} |
| 2 | {4,5} | {5,6} | {5,6} |
| 3 | {6,7} | {7,0} | {7,4} |

An organism is a generation and block index. Its owners are exactly its two
genome-copy vertices. A parent edge between adjacent generations exists
**if and only if** their blocks intersect. No pedigree edges are added without
a witnessing genomic edge.

The positive model uses M0 at even generations and M1 at odd generations.
The proposed negative model uses M0 at generation 0, M1 at generation 1, and
then alternates M0 at even generations with M2 at odd generations.

The repository uses strict, nonempty-path ancestry:

- [SpeciesBridge.lean](../../lean/SamuelAlexanderResearch/SpeciesBridge.lean)
  defines IAP as, for each member, finitely many descendants or finitely many
  non-descendants in the candidate. `Specieslike` additionally requires weak
  connectivity in the induced subgraph and convexity in the ambient graph.
- [SpeciesGlobalIAP.lean](../../lean/SamuelAlexanderResearch/SpeciesGlobalIAP.lean)
  defines an inspecies as a minimal infinite ancestrally closed set and proves
  `whole_inspecies_iff_cofinite_descendants`. Its
  `whole_iap_iff_inspecies_of_infinite_descendants` applies once every vertex
  has infinitely many descendants.

Encode organism `(t,j)` as `4*t+j` to use those exact Nat-based definitions.
Every edge strictly increases this index. Birthdate `t`, or the repository's
index birthdate, has finite sublevels. There are four founders and infinitely
many organisms; each organism has finitely many children. Whole-graph
convexity is automatic. These observations satisfy the graph hypotheses;
they do not identify a biological population.

## Exact transition checks and their all-generation consequence

Rows are parent block indices and columns are child block indices. Matrix
products here are Boolean relational products: OR of ANDs, not real-valued
matrix multiplication. The only transition matrices are

```text
             M0 -> M1                 M1 -> M0
        A = [1 0 0 1]            B = [1 1 0 0]
            [1 1 0 0]                [0 1 1 0]
            [0 1 1 0]                [0 0 1 1]
            [0 0 1 1]                [1 0 0 1]

             M0 -> M2 and M2 -> M0
        D = [1 1 0 0]
            [1 1 0 0]
            [0 0 1 1]
            [0 0 1 1]
```

All four transition types have row sum two and column sum two. Adjacent
matchings share no block, so each of those two incoming edges comes from a
different parent and each of the two outgoing edges goes to a different
child. This proves the degree and no-selfing claims for every generation,
not merely for a checked initial segment.

The exact products are

```text
             [1 1 0 1]
AB = BA =   [1 1 1 0],       ABA = BAB = J4,
             [0 1 1 1]
             [1 0 1 1]

D D = D,
```

where `J4` is the all-ones four-by-four matrix. Because every column of A and
B is nonempty, `J4 A = J4 B = J4`. Induction on additional generations now
proves that, in the positive pedigree, every organism reaches all four
organisms at every generation at least three later. **Three is the tight
uniform mixing depth:** at one step it reaches two organisms; at two steps
it reaches three, never all four.

Consequently every positive-model organism has cofinite strict descendants.
The finitely many generations through `t+2` cover all non-descendants of an
organism at generation `t`. Whole IAP follows; so does whole inspecies by the
existing equivalence. Connectivity also follows by choosing a sufficiently
late common descendant. Whole is therefore specieslike and trivially maximal
among specieslike subsets of this ambient graph.

For the negative model, from generation 2 onward the invariant lane partition
is `{0,1,2,3}` versus `{4,5,6,7}`. Every organism lies in one half. The matrix
D reaches both next-generation organisms in that half and neither organism
in the other half; `D D = D` proves the same at every later generation.
Every vertex at generation 2 or later therefore has infinitely many strict
descendants and infinitely many non-descendants. This falsifies whole IAP,
whole inspecies, and whole specieslike status.

The negative graph nevertheless remains weakly connected. Its first two
generations form the eight-cycle

```text
P0 -- Q0 -- P1 -- Q1 -- P2 -- Q2 -- P3 -- Q3 -- P0.
```

Every later organism has a chain of parents into those generations. This
gives an undirected path into the connected prefix for every vertex.
Connectivity must not be inferred solely from the two tail components, nor
must those components be mistaken for disconnected components of the full
graph.

## Stronger finite-prefix statement

For any prescribed generation N, choose an even S with `S >= max(2,N)`.
Define the negative model to agree with the positive model through generation
S, then use M2 at odd generations after S and M0 at even generations.
The owner maps, and all pedigree edges whose endpoints are in the common
prefix, agree through N. The genomic graph is still identical at every time.
The negative tail argument starts at S; the initial connected prefix is
unchanged. Thus opposite IAP and inspecies status persists after agreement on
any specified finite owner prefix.

Any finite set of owner observations is contained in such a generation
prefix. This establishes a deterministic no-decoder statement for the
observation consisting of this complete unpaired graph plus any prescribed
finite prefix of owner assignments. It does not establish finite-sample
statistical lower bounds or an equality of likelihoods.

## Reproduction and sex assumptions

This is a discrete-generation diploid transmission model with two distinct
parents, allowing consanguineous mating and no recombination on the displayed
interval. A copy has exactly one child copy per generation; each organism
transmits its two different copies to its two children. That is a possible
segregation history, not a typicality or positive-probability assertion about
an entire infinite history under independently randomized meiosis.

Fixed organism sex is possible: give even-index blocks one sex and odd-index
blocks the other. In all four transition types, each child has one parent of
each sex. This assignment is constant for each organism throughout its life.
It also yields **the same sex label on each genomic vertex in both models**:
at even generations the even-sex lanes are `{0,1,4,5}`; at odd generations
they are `{1,2,5,6}`, regardless of whether M1 or M2 is used. Therefore adding
these sex labels does not remove the owner ambiguity. As a further consistency
check, declaring lanes 1 and 5 Y-bearing and the other lanes X-bearing gives
one X and one Y in each even-index block and two X copies in each odd-index
block in all three matchings. No sex-linked sequence or recombination model
has been formalized here; the interval can simply be autosomal.

The infinite genomic graph is **not itself** an instance of the repository's
finite `WongGARG.GARG`. Every finite generation truncation has finite nodes,
acyclic time-oriented edges and nonempty interval annotations, and has unique
local parents. A literal Lean embedding of those truncations into the existing
finite GARG structure is a separate small mapping obligation if that name is
used in the final theorem. Do not silently identify this infinite extension
with Wong's full stochastic model.

## What this sharpens, and what it does not

This construction strengthens the existing sound-projection counterexample
in a specific way: pedigree edges are **exactly** genomic edge images, owner
fibres all have size two, and ordinary biparental degree constraints hold.
It does not reprove the existing transfer theorems. Their ancestry-reflection
premise fails here for a concrete reason: organism paths may switch copies
inside an owner fibre.

For example, the positive pedigree has

```text
(0,P0={0,1}) -> (1,Q0={1,2}) -> (2,P1={2,3}).
```

The first edge is witnessed by lane 1 and the second by lane 2. There is no
genomic path from any copy in the first organism to any copy in the last,
because all genomic paths stay on one lane and the endpoint lane sets are
disjoint. Exact recovery of edges after taking owner images does not imply
reflection of ancestry paths. This is the precise obstruction to applying
the frozen IAP equivalence.

The useful decision is whether a proposed genetic representation preserves
individual ownership, or supplies another condition strong enough to reflect
the required pedigree paths. The theorem warns against interpreting copy
ancestry alone as organism ancestry or species classification. It supplies no
new empirical evidence for speciation, acquired cellular memory, or a
biological mechanism, and settles none of the Royal Society authors' full
questions. The broad fact that grouping or quotienting can create paths is
standard; priority for this particular strengthened construction requires the
separate prior-work review.

## Reproducible bounded check

The following exact Python check was run successfully. It enumerates only
the four local transition types and their relevant products; the induction
above is what justifies all generations.

```python
M = [((0,1),(2,3),(4,5),(6,7)),
     ((1,2),(3,4),(5,6),(7,0)),
     ((1,2),(3,0),(5,6),(7,4))]

def adj(a, b):
    return [[int(bool(set(x) & set(y))) for y in M[b]] for x in M[a]]

def mul(a, b):
    return [[int(any(a[i][k] and b[k][j] for k in range(4)))
             for j in range(4)] for i in range(4)]

for a, b in ((0,1), (1,0), (0,2), (2,0)):
    A = adj(a, b)
    assert all(sum(row) == 2 for row in A)
    assert all(sum(A[i][j] for i in range(4)) == 2 for j in range(4))
    assert all(sorted(i % 2 for i in range(4) if A[i][j]) == [0,1]
               for j in range(4))

for a, b in ((0,1), (1,0)):
    two = mul(adj(a,b), adj(b,a))
    three = mul(two, adj(a,b))
    assert all(sum(row) == 3 for row in two)
    assert all(all(row) for row in three)

for a, b in ((0,2), (2,0)):
    D = adj(a,b)
    assert all(D[i][j] == int(i // 2 == j // 2)
               for i in range(4) for j in range(4))
    assert mul(D,D) == D

def sex_labels(m):
    return {i: j % 2 for j, pair in enumerate(m) for i in pair}

assert sex_labels(M[1]) == sex_labels(M[2])
assert all(sum(i in {1,5} for i in pair) == int(j % 2 == 0)
           for m in M for j, pair in enumerate(m))

print('PASS: degrees, sex constraints, tight mixing, invariant tail')
```

## Minimal acceptance and stopping criterion

Formalize the common genomic graph, owner maps and exact image edges; prove
the local finite identities, the two all-generation consequences, and the
opposite IAP/inspecies endpoint using the existing definitions. Include the
arbitrary finite-prefix parameter if practical; it is the same tail proof.
Record separately whether the finite GARG embedding and sex annotations are
formally checked or only proved in this note. Check prior work before calling
the result novel.

Stop this lane once that scoped result, a clean replay, the prior-work
assessment and an explicit observation contract are preserved. Further general
quotient machinery, stochastic ARG coverage, or model fitting would need a new
reason tied to an identifiable biological question.
