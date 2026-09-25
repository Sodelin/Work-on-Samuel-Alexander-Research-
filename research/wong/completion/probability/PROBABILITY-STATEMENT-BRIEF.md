# Statement-first brief: stopped Big ARG embedded count-chain absorption

Prepared for the next bounded Wong cycle. This packet is separate from the
frozen deterministic 65-endpoint release. Reviewer assignment and compiler
slots are controlled by the programme auditor. Read this brief and the exact
selected statements before inspecting the author's proof bodies.

The mathematical target comes from Wong et al. (2024), Appendix B, paragraph 5
(primary XML section `app2`, printed p. 13). The source describes splitting at
rate k*rho and merging at rate choose(k,2), stopping at one lineage. It states
finite-time termination. This packet addresses the **embedded jump count**;
continuous holding times and a spatial ARG projection are additional targets.

## Exact proposed contract

Let theta be a finite nonnegative real. A Markov kernel on natural counts has
these transitions:

- From 0 or 1, move to 1. State 0 is only a totalization outside positive
  biological count states; state 1 implements the source's stopping rule.
- From k=j+2, move to k+1 with probability theta/(theta+k-1), or to k-1 with
  probability (k-1)/(theta+k-1).

`WongCountChain.pathLaw theta n` is the Ionescu-Tulcea probability measure on
infinite count trajectories constructed from this kernel with initial count
n. The final bridge claims, for every theta and finite n, that almost every
trajectory is eventually identically 1, and hence visits 1 at a finite jump
index. The final endpoints may not assume drift, recurrence, or absorption.
A separately stated intermediate endpoint is allowed to be conditional on a
finite drift witness; it must not be mistaken for the unconditional result.

For literal rates lambda(k)=b*k and mu(k)=a*k*(k-1)/2, assume a>0 and b>=0.
At k>=2 the actual upward/downward singleton masses are to be identified with
lambda/(lambda+mu) and mu/(lambda+mu). The normalized ratio is theta=2*b/a.
The source's displayed convention is a=1, b=rho. The literal-rate final
endpoint starts at n+2; general normalized endpoints also cover n=1 and the
explicit n=0 totalization.

Selected endpoint inventory: 2 scalar drift endpoints, 10 kernel/path-law
endpoints, and 7 unconditional bridge endpoints. These are 19 local checked
endpoints; they are not part of the public deterministic 274 count until a
separate integration and receipt establish that fact.

## Dependency claims to test

The scalar module supplies a finite, nonnegative potential at every natural
state for every finite parameter, after choosing a natural N>=theta. The
count-chain module supplies the actual probability measure and proves its
one-step integral law, rather than assuming a Markov/expectation identity.
The bridge must instantiate the potential and discharge the all-state drift
condition, including states 0 and 1. Its literal-rate algebra must identify
both singleton masses of the actual transition measure.

## Counterexample and source-scope challenges

1. At a=1, b=1, k=2 the upward rate ratio is 2/3, not 1/2. This rejects the
   erroneous normalization theta=b/a. Check casts and predecessor indexing.
2. At b=0, a>0, the positive count descends deterministically by one until 1.
   No division-by-zero exclusion may silently remove this boundary.
3. State 1 is absorbing and has zero transient cost. State 0 moves to 1 and
   incurs one transient step. Check that their Dirac integral inequalities
   are different and that positive starts almost surely avoid zero.
4. Almost-sure finite absorption does not provide a deterministic upper bound
   on the jump count for all paths when b>0, nor termination for every element
   of the ambient trajectory space. Look for an accidental quantifier change.
5. Finite jump index alone does not instantiate continuous holding-time laws.
   State exactly what extra stochastic construction is needed before citing
   finite physical time, nonexplosion or the literal continuous-time ARG.
6. A measure on integer trajectories is not yet the law obtained by forgetting
   the marks and genomic state of a spatial ARG. Do not assume that projection.
7. A coarse finite potential bound is not a proof of the source's exponential
   expected-event asymptotic. Preserve the unresolved rate-normalization issue
   and name the parameter in every expectation or complexity claim.
8. The source stops at one lineage. This is not a stationary birth-death model
   that continues splitting from count one; challenge any use beyond that
   stopping convention.

## Deliverable and stopping condition

Return attempted counterexamples, exact hypotheses that defeat them or a
minimal failing witness, and a source correspondence verdict. Verify whether
the final statement assumes the conclusion through a hidden drift premise.
Separate a manual statement review from kernel verification and from public
CI. Stop with PASS WITH SCOPED LIMITS or a concrete blocking declaration. Do
not edit the implementation, start Lean without its slot, or fan out further.
Write only the review artifact assigned by the auditor.