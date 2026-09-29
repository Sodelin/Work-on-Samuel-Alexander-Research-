# When a discarded detail changes the next answer

General-connections cycle 1, 25 September 2026. **Written mathematical bridge with bounded executable checks; reused Q04/Q09 proof evidence.** Prepared for the programme auditor. No whole source question is closed.

Consider two systems that currently display 0. One carries memory 0; the other carries memory 1. Waiting can leave their displays indistinguishable. An intervention that reads the memory into the display makes them respond differently. A description containing only the current display cannot predict both responses correctly.

This packet makes that observation precise in two deliberately chosen models: a finite cell-state toy and a decision device retaining a finite record of arbitrary length. Both have the same exact four-state description. This is useful because it identifies which information may be discarded for a declared prediction task, and which intervention makes a discarded distinction necessary.

The word “cell” supplies a possible interpretation of variables, not an experimentally fitted cellular mechanism. The decision device has no utility function or claim to optimal choice. Neither model is presented as a theorem stated by Levin or Friston.

## A worked example before the theorem

The cell toy has state $`(v,m,n)`$: visible response $`v`$, regulatory-memory bit $`m`$, and nuisance bit $`n`$. The decision toy has state $`(v,h)`$: current output and a finite binary record. Its relevant memory is the parity of the number of 1s in that record.

Starting with zero visible output and zero memory, these systems give the following exact trace. Record entries in brackets are binary symbols, not probabilities.

| Applied action | Cell state $`(v,m,n)`$ | Decision state $`(v,h)`$ | Shared description |
|---|---|---|---|
| initial | $`(0,0,0)`$ | $`(0,[])`$ | $`(0,0)`$ |
| prime | $`(0,1,1)`$ | $`(0,[1])`$ | $`(0,1)`$ |
| wait | $`(0,1,0)`$ | $`(0,[1,0])`$ | $`(0,1)`$ |
| probe | $`(1,1,1)`$ | $`(1,[1,0,0])`$ | $`(1,1)`$ |
| prime | $`(1,0,0)`$ | $`(1,[1,0,0,1])`$ | $`(1,0)`$ |
| probe | $`(0,0,1)`$ | $`(0,[1,0,0,1,0])`$ | $`(0,0)`$ |
| reset | $`(0,0,0)`$ | $`(0,[])`$ | $`(0,0)`$ |

The cell's nuisance bit changes throughout. The decision record can keep growing. Neither detail is needed to predict the shared description under the four actions defined below. The retained memory bit is needed.

## Where the question comes from

Abramsky et al. ask in section 4.2, published p.11, when generating a result can be separated from the result by projection. The programme records that question as Q04. Our selected interpretation asks when a state projection supports exact controlled next-state prediction. A projection remains a perfectly valid function when that predictive property fails; we have not proved that projection itself is impossible. [Published paper](https://doi.org/10.1098/rsos.261059); [pinned Q04/Q09 ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/problem-ledger.json).

The supplied Levin transcript reports memory and forgetting behavior in mathematical molecular-network models, at lines 313–351, about 31:01–34:50. It motivates asking which state an intervention changes or leaves behind. The supplied Friston transcript discusses selecting actions to reduce uncertainty about states, parameters and model structure, at lines 392–414, about 49:31–52:08. It motivates explicitly specifying a discriminating intervention. These passages supply motivation, not our Boolean transition rules, parity summary, or their empirical validation. [Levin lecture](https://www.youtube.com/watch?v=Or_3tlEOLj4); [Friston lecture](https://www.youtube.com/watch?v=Fus2k7F5iN4). Exact local source identities and current reading scope are in [SOURCES.md](SOURCES.md).

## The preservation criterion reused from Q04

Let $`X,A,Y`$ be sets, let $`T:A\times X\to X`$ be a deterministic controlled transition, and let $`p:X\to Y`$ be surjective. Write $`T_a(x)=T(a,x)`$. Then

```math
\begin{aligned}
&\exists!\,F:A\times Y\to Y,\quad
  \forall a\in A\ \forall x\in X,\quad
  F(a,p(x))=p(T_a(x))\\
&\quad\Longleftrightarrow\quad
\forall a\in A\ \forall x,x'\in X,\quad
p(x)=p(x')\ \Rightarrow\
p(T_a(x))=p(T_a(x')).
\end{aligned}
```

A fibre is the set of detailed states with one observation value. The condition says every state in a fibre must produce the same next observation under the same action.

Necessity follows by evaluating the same $`F(a,p(x))`$ for both states. For sufficiency, define $`F(a,y)`$ using any representative of the fibre over $`y`$; the condition makes the result independent of the representative. Surjectivity supplies representatives and fixes the value at every $`y`$, proving uniqueness. For arbitrary sets this existence argument uses classical choice in the existing Lean implementation; the concrete maps below are explicit.

If $`p`$ is not onto, replace $`Y`$ by $`p(X)`$. Values at unused elements of $`Y`$ are not determined. For example, identity dynamics on $`X=\{0,1\}`$, observed by inclusion into $`\{0,1,2\}`$, permits two exact extensions sending 2 respectively to 0 and 1. Both agree on every actual observation.

For every input sequence $`u:\mathbb N\to A`$, every initial $`x_0`$, and every $`t\in\mathbb N`$, the recurrence $`x_{t+1}=T_{u(t)}(x_t)`$ projects to $`z_{t+1}=F(u(t),z_t)`$, with $`z_0=p(x_0)`$. This follows by induction. It preserves the observed trajectory under the same inputs; it does not justify letting two hidden-state controllers choose different inputs and then asserting equal outcomes.

**Formal evidence reused:** existence is ExactAbstraction.exact_factor_iff, uniqueness is exact_factor_unique, and trajectory preservation is trajectory_preservation/compatible_gives_trajectories, source lines 14–67. [Pinned Lean module](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean#L14). The present toy instantiations and refinement argument below have written proofs and finite checks; they have not received new Lean verification.

## Two complete model definitions

Let $`B=\{0,1\}`$, $`A=\{\mathrm{wait},\mathrm{prime},\mathrm{probe},\mathrm{reset}\}`$, and $`Z=B^2`$. All four actions are enabled at every declared state. We treat them as specified interventions, not action labels inferred from observational data.

For the cell toy, let $`X_c=B^3`$, $`p_c(v,m,n)=v`$, and $`q_c(v,m,n)=(v,m)`$. These are hypothetical discrete states at a chosen sampling interval. The prime action toggles a bit by definition; its name is not a biological efficacy claim.

For the decision toy, let $`X_d=B\times B^*`$, where $`B^*`$ is the set of all finite binary words, including the empty word $`\epsilon`$. Define
$`\mu(h)=\sum_i h_i\bmod 2`$, $`p_d(v,h)=v`$, and $`q_d(v,h)=(v,\mu(h))`$. The record may have arbitrary finite length. Appending 0 records an event with no memory toggle; appending 1 records a toggle.

| Action $`a`$ | Cell transition $`T^c_a(v,m,n)`$ | Decision transition $`T^d_a(v,h)`$ | Shared transition $`F_a(v,m)`$ |
|---|---|---|---|
| wait | $`(v,m,1-n)`$ | $`(v,h0)`$ | $`(v,m)`$ |
| prime | $`(v,1-m,1-n)`$ | $`(v,h1)`$ | $`(v,1-m)`$ |
| probe | $`(m,m,1-n)`$ | $`(\mu(h),h0)`$ | $`(m,m)`$ |
| reset | $`(0,0,1-n)`$ | $`(0,\epsilon)`$ | $`(0,0)`$ |

Here $`h0,h1`$ mean append one symbol. These definitions give fixed transition semantics on each whole state space. An unbounded record does not imply open-ended changes to a language or metamodel.

**Cell application.** The projection $`q_c`$ is onto: $`(v,m,0)`$ represents every $`(v,m)`$. Each row directly gives
```math
q_c(T^c_a(x))=F_a(q_c(x)).
```
The nuisance bit can therefore be erased for this prediction task, even though it changes at every step.

**Decision application.** The projection $`q_d`$ is onto: use $`h=\epsilon`$ for $`m=0`$ and $`h=[1]`$ for $`m=1`$, independently of $`v`$. The identities
```math
\mu(\epsilon)=0,\qquad \mu(h0)=\mu(h),\qquad
\mu(h1)=1-\mu(h)
```
establish $`q_d(T^d_a(x))=F_a(q_d(x))`$ for all four actions and every finite word. Thus the complete record may be replaced by its parity for this task. This is an all-length written argument; checking finitely many records alone would not establish it.

**Actual model-to-model bridge.** If $`q_c(x_0)=q_d(y_0)`$, then for every common input sequence and every time $`t`$,
```math
q_c(x_t)=q_d(y_t).
```
Apply the reused trajectory result to each commuting map and the common $`F`$. There is no bijection between the eight-state cell space and the countably infinite decision space. The relation $`q_c(x)=q_d(y)`$ is preserved action by action. Matching outcomes do not identify which internal mechanism is present. Both models were deliberately constructed to implement this common description. The value of the example is the explicit sufficiency test and the change of action set that breaks a coarser description.

## What the abstraction fee means here

With only $`A_0=\{\mathrm{wait},\mathrm{prime},\mathrm{reset}\}`$, the coarse observation $`p_s=v`$ is already exact in either model:
```math
F^0_{\mathrm{wait}}(v)=v,\quad
F^0_{\mathrm{prime}}(v)=v,\quad
F^0_{\mathrm{reset}}(v)=0.
```
Even repeated hidden priming cannot affect the chosen output when no admitted action reads it.

Adding probe invalidates that reduction. Cell states $`(0,0,0)`$ and $`(0,1,0)`$ have the same $`p_c`$, but their next $`p_c`$ values are 0 and 1. Decision states $`(0,\epsilon)`$ and $`(0,[1])`$ have the same $`p_d`$ and the same mismatch after probe. The relevant visible/memory pairs can also be reached from the displayed zero initialization by reset and reset-followed-by-prime; the cell nuisance value may differ and is irrelevant to this witness.

A deterministic predictor fed only the same current visible output and probe must return one answer. It is wrong for at least one member of each witness pair. That is the exact prediction-relevant loss caused by simplification in this packet. No probability distribution, average error rate, entropy, thermodynamic expenditure, or universal numerical fee is inferred.

### Exact meaning of “coarsest”

Fix either model $`s`$. An exact observation refinement retaining the visible output is an onto map $`r:X_s\to W`$, together with a decoder $`d:W\to B`$ and transition $`G:A\times W\to W`$, satisfying
```math
p_s=d\circ r,\qquad
r(T^s_a(x))=G_a(r(x))\quad\text{for every }a,x.
```
Restricting $`W`$ to $`r(X_s)`$ handles a competing map that was not originally onto.

Write $`q_s\preceq r`$ when $`q_s=H\circ r`$ for some $`H:W\to Z`$: knowing $`r`$ then determines $`q_s`$. In this order, “coarsest” means an exact refinement of $`p_s`$ that is no more informative than every other exact refinement of $`p_s`$, for the specified action set and prediction target.

Here $`q_s(x)=(p_s(x),p_s(T^s_{\mathrm{probe}}x))`$. Consequently the explicit decoder
```math
H(w)=\bigl(d(w),d(G_{\mathrm{probe}}(w))\bigr)
```
satisfies $`H(r(x))=q_s(x)`$. Since $`q_s`$ is itself exact and retains $`p_s`$, it is a coarsest exact refinement.

Both $`q_s`$ attain all four values of $`B^2`$, so any such $`r`$ must attain at least four values. Within each fixed visible value, one binary distinction must survive. This is minimal state distinguishability for these interventions, not a Shannon-bit estimate or a claim about minimal physical or cognitive systems. The proof does not compare control loops with genealogical ancestry graphs.

## Tests that could invalidate the interpretation

The intended collision under coarse $`p_s`$ confirms that erasing memory is unsafe. Two deliberately invalid variants test the more important sufficiency assumption.

- If cell probe instead returns visible $`m\mathbin{\mathrm{xor}}n`$, equal $`q_c`$ states with different $`n`$ have different next visible outputs. Erasing nuisance $`n`$ is then unsafe.
- If decision probe reads the last recorded symbol instead of parity, histories $`[1]`$ and $`[1,0]`$ share parity 1 but produce different visible outputs. The parity summary is then insufficient.

Both variants fail the executable compatibility check. These are counterexamples to extending our selected model claim after changing its assumptions; they are not counterexamples to biological research or to Q04.

The existing Q09 module gives another manifestation of the same failure pattern: two binary merge histories have the same current membership partition, but predecessor-restoring split produces different partitions. Its witness and impossibility statements appear at lines 117–162. [Pinned merge-history module](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean#L117). Our one-bit history summary does not repair that model automatically; a different action semantics can require different retained history. Q09's controller, payoff and scheduler gaps remain unchanged.

## Prior work, evidence and empirical limits

This is established quotient/congruence mathematics. Givan, Dean and Greig define quotient models in section 2.2, give a finite-machine quotient result in section 3.2/Theorem 2, and study actionwise block-transition preservation for MDPs in section 3.3. Their Theorem 7 includes optimal-policy transfer under reward-preserving stochastic bisimulation. Our deterministic equations are a special-case preservation pattern; they do not supply reward preservation or a policy-optimality theorem. We inspected these definitions and theorem statements, not the entire paper or all proofs. This identifies direct prior work without establishing priority for every formulation here. [Author-hosted manuscript](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf).

The source intake already provides a broader written, independently reviewed stochastic transport result. This packet adds explicit examples, the intervention-dependent obstruction, and the exact refinement order. It neither replaces that result nor counts another proof of Q04 as a new research discovery. An existing broader synthesis in the internal Friston-Levin intake is cited as context only; it is not included in this public packet, and this packet makes no public reproduction claim for it. This cycle has not independently re-audited its full proof.

The current author-run executable check records:

| Check | Actual scope/result |
|---|---|
| Commuting equations | All 32 cell state/action pairs; 120 decision pairs with initial record length at most 3 |
| Cross-model trajectories | 20,460 related-pair/action-word cases, lengths 0–4; 95,580 prefix comparisons |
| Finite partition search | All 225 refinements of visible $`v`$ on eight cell states; minimum 2 blocks for $`A_0`$, 4 for $`A`$ |
| False-variant controls | Both altered probe variants rejected |
| Nonsurjective control | Distinct reduced extensions agree on the observation image |
| Reused proof provenance | Both downloaded module SHA-256 values match the pinned prior Lean receipt |

[Check source](check_models.py) and [full finite receipt](FINITE-CHECKS.json) make the bounds explicit. This is self-checking evidence, not independent review. The arbitrary-record and all-horizon results rest on the written identities and induction. The pinned prior receipt reports 16 selected Lean endpoints and no sorryAx; this cycle ran zero Lean processes. [Pinned receipt](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/exact-abstraction/PUBLIC-VERIFICATION.json).

An empirical use would require evidence that the selected state includes relevant controller, environmental and memory variables; that each physical intervention implements the stated transition; that the measurement can distinguish the retained states; and that determinism and stationarity are appropriate at the chosen sampling interval. Equal observational data do not establish the intervention equations. If noise matters, compare next-observation distributions using the existing stochastic contract. No fitted kernels, physical intervention data, consciousness conclusion or universal-systems claim is supplied here.

## Checkpoint and one next proof obligation

The bounded deliverable is complete as a written bridge plus explicit obstruction and finite checks. Its practical output is a criterion for changing an abstraction when the admitted intervention set changes.

**Only next proof obligation, routed to the auditor's shared proof worker:** mechanize the generic factorization lemma used for coarseness. Given $`q(x)=(p(x),p(T_{\mathrm{probe}}x))`$, $`p=d\circ r`$, and $`r(T_a x)=G_a(r(x))`$, prove
```math
q=\bigl(w\mapsto(d(w),d(G_{\mathrm{probe}}w))\bigr)\circ r.
```
This is written-only until the owning worker actually checks a declaration. No compiler work or agent dispatch was started here. Publication, independent final acceptance and any empirical follow-on belong to the auditor. This task remains visible and unarchived.

