# Internal statement audit: affinity fixation rate

Date: 2026-09-25. **PASS for the stated deterministic model and assumptions**, with two presentation notes below. This is an independent internal AI statement/proof review, not external peer review, a novelty assessment, or a new compiler run. No proof source was changed. The saved validation receipt reports exit 0 for the base and fixation modules; the fixation log lists nine selected declarations using only `propext`, `Classical.choice`, and `Quot.sound`.

Reviewed inputs: `affinity-lean/FogartyAffinity.lean`, `affinity-lean/FogartyAffinityFixation.lean`, and `FOGARTY-GLOBAL-RATE.md`.

1. **The theorem starts from the source update.** Base definitions at lines 30–55 encode the four AB, Ab, aB, ab frequencies, transmission, normalization, and selection recursions. `transmit_q` equates the normalizer's cultural marginal with y1+y3. In the fixation file, `transmit_margin_one/two` and `source_contracts_odds` derive the common odds bound from these recursions and simplex preservation. Odds contraction is a conclusion, not a disguised premise. The initial odds condition is explicit and separately justified.

2. **Arbitrary affinity sequences are covered.** `trajectory_odds_bound` (line 96), `trajectory_fixates` (145), and `model_global_fixation` (217) quantify over b1,b2 : Nat → Real, requiring only that both lie in [0,1] at each generation. Neither constancy, convergence, independence, nor smoothness is assumed. This covers a realized adaptively or state-dependently chosen admissible sequence. It is not a stochastic measurability theorem. Selection is one constant s; actual convergence requires s>0. The finite bounds also hold for s=0, without then yielding fixation. The manuscript correctly marks varying affinities as an extension of the published fixed-parameter model.

3. **Initial positivity is correctly scoped.** `positive_backgrounds_odds` (180) needs only x1(0)>0 and x3(0)>0, besides the simplex constraints, to construct r=max(x2/x1,x4/x3). x2 and x4 may be zero. Strict positivity of all four frequencies is sufficient, not necessary. The subsequent proof propagates inequalities without dividing by later x1 or x3. The more general `OddsBound` endpoint also permits an absent genetic background when both corresponding frequencies vanish; no assertion is made that the condition is necessary for convergence.

4. **The finite-time deficit and actual limit are established.** With r_n=r/(1+s)^n, the checked `trajectory_odds_bound` gives both coordinate inequalities. `trajectory_simplex` and `odds_deficit_sharp` (110) then give 1−q_n ≤ r_n/(1+r_n); `odds_deficit` supplies nonnegativity and the weaker ≤r_n bound. This is exactly the manuscript's formula with c=1/(1+s). `CultureFixates` (141) is an explicit epsilon definition, and `trajectory_fixates` proves it using geometric decay. Uniformity is over admissible affinity sequences for fixed initial r and fixed positive s, not over unbounded r or s approaching zero.

5. **A constructed trajectory is included.** `evolve` (198) recursively applies the normalized `step`; `evolve_simplex` and `evolve_recursions` verify its admissibility. `model_global_fixation` therefore proves the finite bound and convergence for an actual defined evolution, beyond an implication about a hypothetical trajectory satisfying recursions.

Presentation notes: the manuscript's opening still says Lean verification is in progress; the final saved receipt now reports PASS. Also, `model_global_fixation` packages the weaker r_n deficit and convergence. The sharper r_n/(1+r_n) deficit is an immediate composition of checked lemmas, not a separately packaged final declaration. Neither point changes the mathematical result, but declaration-level coverage should be described accurately.

The quantity converging to one is the cultural B frequency q, not the genetic A frequency p. The result does not establish genetic fixation, speciation, finite-population fixation, or exact attainment of q=1 at a finite time. The manuscript preserves these limits. No mathematical discrepancy was found within this bounded review.

Reviewed SHA-256 values:

- FogartyAffinityFixation.lean: `CA38BDF620CB37B7DF466E403F903A7C3A0E3905EBB2356FC1099398FFE661F7`
- FogartyAffinity.lean: `C9E406C2273B3374BBCF08B7144E0BB83C156462AA22319F09F8D74328B2FDF3`
- FOGARTY-GLOBAL-RATE.md: `6778CE4B5C810F879E0CE0F5559616A8BEAF86D87FC022588D7FC0EA5CC759E6`
