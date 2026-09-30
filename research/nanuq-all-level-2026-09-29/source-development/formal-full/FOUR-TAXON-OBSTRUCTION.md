# Four total taxa do not certify the parameter family

The focused reconstruction passed. For the parameter choice `(c,s,a,o)=(1,1,1/2,1)`, all 117 anchor coefficients on the saved three- and four-taxon systems are nonnegative. The saved five-taxon paired-tip system below has coefficient `-1`. Thus the proposed universal parameter certificate cannot be reduced to at most four total taxa merely by checking all such restrictions.

The exact saved witness is `taxa=5`, `duplication_mask=1`, `pattern=4717`, anchors `(0,1)`, gaps `(2,4)`. Its expanded tip labels are `[0,0,1,2,3,4]`. Calling `systems(5,1)` only, and selecting the indicated pattern, reconstructs the position-labelled plane tree

```
[0, [[[1,2],3], [4,5]]]
```

Position 0 is the root-adjacent tip. Positions 0 and 1 are the adjacent copies of taxon 0; positions 2 through 5 have labels 1 through 4. An independent graph-distance four-point reader, with both possible global copy choices checked explicitly, recovers packed pattern 4717 and the quartet codes `[5,5,1,1,1]` in lexicographic quartet order. No larger tree families or random networks were enumerated.

For gaps `(2,4)`, their successors are `(3,0)`. The four anchor entries are:

| Entry | Category | Value |
| --- | --- | --- |
| `M(2,4)` | Adjacent queried pair in a two-topology quartet | `2a=1` |
| `M(3,0)` | Shares an anchor | `1` |
| `M(2,0)` | Shares an anchor | `1` |
| `M(3,4)` | Cherry pair in a singleton quartet | `2c=2` |

Consequently the actual unhalved coefficient is

`alpha = M(2,4)+M(3,0)-M(2,0)-M(3,4) = 2(a-c) = -1`.

Its normalized inequality is the saved row `[0,-1,0,1,0]`, namely `a-c≥0`. The factor two explains the distinction between the row evaluation `-1/2` and the raw coefficient `-1`.

The exact rational receipt is `FOUR-TAXON-OBSTRUCTION.json`; the reproducible focused script is `check_four_taxon_obstruction.py`. The receipt hashes the source scripts and saved datasets. It checks all 9 coefficients on the saved three-taxon system and all 108 on the three saved four-taxon systems, each with minimum zero.

This is a counterexample to four-total-taxon certification of the full parameterized anchor-positivity criterion within the actual paired-tip representation. It is not a counterexample at the original NANUQ parameter choice, and it is not a necessity result for an aggregated unweighted source-network distance. It does not prove that six total taxa rather than five are necessary: the available symbolic receipt has the same sixteen rows at five and six taxa, but a reduction theorem would still be required. Nor does it refute a four-ordinary-leaf bound: this example contains four single-copy taxa plus one duplicated taxon. Those different meanings of the proposed bound must stay separate.