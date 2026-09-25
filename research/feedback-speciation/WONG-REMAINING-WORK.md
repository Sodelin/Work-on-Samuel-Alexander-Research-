# Separate unfinished Wong formalization

Status checked 2026-09-25 after the user's direct question. The Wong paper is **not fully formalized**.

Source: Yan Wong et al., *A general and efficient representation of ancestral recombination graphs*, Genetics 228(1), iyae100 (2024), [DOI](https://doi.org/10.1093/genetics/iyae100).

The authoritative source coverage map is in the existing project:
C:/Users/Owner/Documents/Codex/2026-09-24/alexander-formalization/notes/WONG-ALEXANDER-BRIDGE-STATUS.md

Substantial interval-graph, local ancestry, sample restriction, contraction, reconstruction-boundary and finite/infinite completion mathematics is already checked. Whole-paper completion still includes additional executable-algorithm/event-encoding obligations and specified stochastic-process statements. Biological mapping and empirical/software-performance claims need their own evidence.

The public-writing task titled **Explore broader uses for this idea**, thread 01a0d68e-5582-7333-bdf8-78e6327f5174, has taken ownership of the remaining source-faithful Wong formalization as a separate user-requested goal. This feedback/speciation lane will not duplicate that implementation. Completing this package must not be reported as completing Wong.

The earlier phrasing "self-similar graphs" was too broad: the checked interval property is ancestry constancy between genomic breakpoints. It is not a universal scaling symmetry.

The finite/infinite completion theorem is also a genuine limitation, not an unfinished proof that can be filled in: without added future assumptions, the same finite graph has completions with opposite whole-population specieslike status. A stronger positive inference requires explicit additional hypotheses, such as the separate pedigree conditions being studied here.
