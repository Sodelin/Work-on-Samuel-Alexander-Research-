# A biological evidence contract for the stochastic theorem

This note adopts the coordinated evidence lane's bounded source audit of
27 September 2026. That lane owns literature/data acquisition; this track
owns the [mathematical contract](STOCHASTIC.md) and canonical ledger. Source
identifiers, hashes and retrieval limits are preserved in
[STENTOR-SOURCE-RECEIPT.json](verification/STENTOR-SOURCE-RECEIPT.json).
No new biological fit or experiment is reported here.

## What the primary study contributes

Rajan et al., *Molecular pathways for learning in the single-cell Stentor
coeruleus*, Current Biology 36, 2367–2381.e9 (2026),
[DOI 10.1016/j.cub.2026.03.080](https://doi.org/10.1016/j.cub.2026.03.080),
combines molecular perturbations and behavioral controls. Mechanically
habituated cells retain electrical-stimulus responsiveness, including in the
tested puromycin condition. This makes **probe identity** relevant to the
proposed predictive state. The paper's parent–progeny comparison begins with
69 dividing cells and compares responses before and after division during
continued stimulation, selecting anchored, unobscured cells. It is not
assignment of sister cells to different histories. The omics are exploratory
and the proposed receptor network is hypothetical. See the
[primary manuscript](https://pmc.ncbi.nlm.nih.gov/articles/PMC13192338/),
Results and transgenerational Methods.

These are experimental findings and a proposed mechanism, separate from the
invented Lean models. Parent–progeny response association is compatible with
stable differences between cells, acquired state, shared context and
selection. It does not by itself identify a changing memory variable.

This is also a different study from the
[Stentor reviewed preprint discussed earlier](https://doi.org/10.7554/eLife.112314.1).
Evidence from their different protocols and authors must not be pooled as if
it were one experiment.

## What can currently be reproduced from the checked public routes

The [Dryad record](https://datadryad.org/dataset/doi:10.5061/dryad.z34tmpgrm)
lists approximately 414.90 GB of sequencing files. The bounded audit read its
inventory and metadata without downloading raw sequencing. The
[author code at the pinned commit](https://github.com/aralbright/2025_stentor_learning/tree/6411b40e31dfce250445d7b1ff4c26e32823dd4e)
has a complete 24-file tree; `conditions.csv`, read by the scripts, is absent
from that tree. The `exp1` script explicitly excludes `R1c` and `B1a` in
different comparisons. The inspected filtered author tables have 489 and
138 rows. These are inspections of author outputs, not our fitted results.

The checked routes did not establish a public table linking individual
behavioral responses, assigned histories and parent–daughter identities.
That is a bounded access finding, not a claim that such records do not exist.
The completed small-data follow-up reconstructed all 21 `exp2` condition
labels and validated exact sample-key joins for the 15 retained matrix
columns. It did not recover the original batch mapping. One earlier sample,
`R3c`, has an unresolved conflict between its deposited label and surrounding
naming pattern; it was not silently relabeled. Six later untrained controls
are absent from the processed matrix. These repairs improve reuse of author
outputs without supplying missing longitudinal behavioral records.

The follow-up also recovered the actual 19-hour estimate for the candidate
`SteCoe_6763`, superseding mere absence from a filtered list. It is not a
detectable difference in those author comparisons, which does not establish
a zero effect. Duration, stimulation frequency and source culture change
together across the four-hour and 19-hour regimes, so their difference is
not an isolated duration effect. Likewise, an author control table with no
discoveries does not establish equivalence of controls. These are bounded
audits of author-fitted outputs, not a new RNA fit or mechanism validation;
the source receipt preserves the follow-up's exact values and input hashes.

## The proposed discriminator

Specify two histories, one common post-history probe, and a matched elapsed
time and context. The target is a **response distribution**, with a declared
response window. Seek records containing:

- Baseline cell/lineage IDs and pre-assignment measurements.
- History assignment, its unit and allocation mechanism, culture/run and time.
- Probe identity, intervention/control identity, and all eligible outcomes.
- Division, detachment, viability, loss to view and every exclusion by arm.

The proposed contrast is between response laws under assignment to each
history and the same probe, conditional only on declared baseline variables.
Random allocation at the appropriate unit, or another justified identification
argument, is needed. Cells in a jointly treated dish are not automatically
independent experimental replicates. Paired lineages may help control stable
differences, but shared exposure, carryover and timing remain explicit issues.
Keep time-matched controls and their uncertainty; vary duration and frequency
separately within culture/run blocks when those effects are the target.

Do not identify a history effect by selecting cells on a **post-history
visible state affected by training**. Our [selection counterexample](BIOLOGY.md)
shows why this can select different stable types even after randomization.
The same concern applies to conditioning on division, attachment or continued
visibility. An effect at a controlled post-history state, or in a specified
principal stratum, is a different causal question with additional assumptions.

A reproducible common-probe difference would challenge a declared
history-insensitive response model under these design assumptions. It would
not uniquely identify a molecular storage mechanism. That needs selective
measurements or perturbations and controls for direct probe effects and
general responsiveness.

## Connection to the formal result and the remaining gate

`joint_sensor_observed_law` tells us what a specified stochastic model must
preserve to transfer predictions of this sort of adaptive experiment. It
does not prove that the measured system has the stipulated Markov state or
that estimated transition kernels are correct. The six-state example also
shows how a mixture of response programs and an internal random transition
can share all admitted output traces. Additional informative probes or
measurements are needed to distinguish such explanations.

Admit a biological model correspondence only after naming its latent state,
measurement, intervention family, initial sampling law and controller
information, then supplying evidence for the preservation assumptions. Admit
a new fit only after the record-level linkage and allocation support its
estimand. Until then the model, fit and mechanism claims remain separate.
