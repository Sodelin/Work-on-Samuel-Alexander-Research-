# Prior-art audit: directed line graph and the three-root cap-two avoider

**Finding.** Replacing each original directed edge by a vertex and linking consecutive edges is the classical **line digraph** (also called an arc digraph). Its use here is a standard recoding, not a new graph operation. Applied to the pinned manuscript's binary edge-labelled avoider, however, it gives a precise vertex-gendered corollary omitted from that manuscript: **three roots, two children per vertex, two differently gendered parents per non-root, and avoidance of the same non-eventually-periodic binary sequence**. The bounded search below did not verify an earlier explicit statement of that exact corollary; it does not establish priority.

## Classical source and what it actually says

[Harary and Norman, *Some properties of line digraphs* (1960)](https://link.springer.com/article/10.1007/BF02854581) is an early primary publication for the named operation (journal metadata verified; the publisher exposed only a subscription preview, so its detailed text was not inspected). [Orlin, *Line-digraphs, arborescences, and theorems of Tutte and Knuth* (1978)](https://www.sciencedirect.com/science/article/pii/0095895678900382) is a later primary paper whose abstract explicitly defines the operation: original arcs become vertices, with an arc between them when the first head equals the second tail, and says it extends Harary-Norman's characterization. The 1978 full text was not accessible through the web tool; the abstract supplies the definition. The color transfer also has explicit prior art: [Xu, *Matrix Representations and Extension of the Graph Model for Conflict Resolution* (2009), pp. 111, 114](https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/d22cf3b3-7dc8-475e-bd26-66f768d26c85/content) describes a transformation from an edge-weighted colored multidigraph to a vertex-weighted colored line digraph and illustrates edge labels becoming vertex labels. The biological avoidance and degree counts below are a separate application of that familiar recoding.

For an original arc $`e=(u,v)`$, the new vertex's children are exactly the original arcs leaving $`v`$. Hence the exact identity

```math
\deg^+_{L(P)}(e)=\deg^+_P(v).
```

This is why the directed construction preserves an original outdegree cap. The undirected line-graph degree formula would be the wrong comparison.

## Exact application to the pinned avoiding population

The [pinned classification manuscript, §2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md) defines $`P_s`$ on $`\mathbb N`$ with roots 0 and 1. For each $`v\ge2`$ it has two incoming arcs $`v-1\to v`$ and $`v-2\to v`$ with complementary binary edge labels. Vertex 0 has one child; every original vertex $`v\ge1`$ has two. The manuscript proves that if an infinite path spells target $`s`$, then $`s`$ is eventually periodic. Thus a non-eventually-periodic $`s`$ is avoided from **every** starting vertex, not only the roots.

Form $`L(P_s)`$ with a vertex for each original arc $`e`$, an adjacency $`e\to f`$ exactly when $`\operatorname{head}(e)=\operatorname{tail}(f)`$, and permanent vertex gender $`\gamma(e)=g(e)`$, the original edge label. Give $`e=(u,v)`$ birthdate $`v`$.

| Population property | Calculation for $`L(P_s)`$ |
|---|---|
| Roots | A line vertex $`e=(u,v)`$ is parentless iff $`u`$ is an original root. These arcs are exactly $`0\to2`$, $`1\to2`$, and $`1\to3`$: **three roots**. |
| Parents and genders | If $`u\ge2`$, its two incoming original arcs have complementary labels. They are the two parents of every line vertex whose tail is $`u`$, so each non-root has exactly two parents, one of each permanent vertex gender. |
| Children | For every line vertex $`e=(u,v)`$, $`v\ge2`$, and $`v`$ has exactly two outgoing original arcs. Thus **every line vertex has exactly two children**. |
| Birthdates | Along $`(u,v)\to(v,w)`$, $`v<w`$. Each integer birthdate $`v`$ has only two arc-vertices, so all real birthdate sublevel sets are finite. |
| Infinitude | $`P_s`$ has infinitely many arcs, hence $`L(P_s)`$ infinitely many vertices. |
| Avoidance | A line path $`e_0,e_1,\ldots`$ is exactly a consecutive original edge path, and its vertex genders are $`g(e_0),g(e_1),\ldots`$. It spells $`s`$ iff the original edge path spells $`s`$. The manuscript's avoidance proof therefore transfers verbatim. |

The shifted start convention matters: the first line vertex represents the **first original edge**, so there is no dropped first symbol. The population model permits paths from any vertex; it does not demand a root start. The absence of $`0\to1`$ is also material to the three-root count.

## Comparison with the manuscript's two-copy lift

The [same pinned manuscript, §3](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md) gives each original vertex one copy per alphabet symbol and labels a copy by that symbol. In the binary case it explicitly reports **four roots and at most four children per vertex**, alongside the smaller edge-labelled two-root/two-child construction. That section does not state the directed line-graph recoding or the resulting **three-root/two-child vertex-gendered** consequence. The line graph is therefore a tighter consequence of the manuscript's own $`P_s`$, not a replacement proof of its central classification theorem. Its advantage is preserving the outdegree cap while making gender permanent on vertices; it increases the root count from two to three.

## Source limits and attribution

The classical operation, path recoding, and transfer of edge labels to line vertices have prior art. The exact degree and population checks above are direct deductions from the pinned $`P_s`$ formulas; no separate publication asserting this specific biological-unavoidability corollary was located in the bounded searches (`"biologically unavoidable" "three roots" "two children"`, `"vertex-gendered" "line digraph"`, and related phrases). Negative search results do not show that none exists. Alexander's [2013 source paper](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i1p31) introduced the population model and allowed vertex-gendered special cases, but the current audit does not claim to have exhaustively searched all later graph-theory or symbolic-dynamics literature. The defensible novelty statement is narrow: **this exact cap-two vertex-gendered corollary is not explicit in the pinned manuscript and follows by a classical construction**.
