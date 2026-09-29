# A uniform fixation bound for the affinity-bias model

Date: 2026-09-25. Written proof independently checked internally. Lean verification passed for the source recursions and the global-fixation module; the aggregate receipt records the final packaged sources. A separate internal statement review also passed. This is a source-model refinement; its priority is unestablished. It is not a claimed solution of an author-designated open conjecture.

## Exact model and question

Fogarty, Zhang and Feldman, [Gene-culture association and coevolution](https://doi.org/10.1016/j.tpb.2025.08.003), Table 2 and equations (17)–(23), define a haploid genetic locus A/a and a cultural trait B/b. Write the four frequencies as x1,x2,x3,x4 for AB,Ab,aB,ab. They are nonnegative and sum to one. Set p=x1+x2, q=x1+x3 and D=x1*x4−x2*x3.

Cultural transmission with affinity parameters b1,b2 in [0,1] produces

    y1=x1−b1*D,  y2=x2+b1*D,
    y3=x3+b2*D,  y4=x4−b2*D.

Positive selection s>0 for B then gives

    x1'=(1+s)*y1/Gamma,  x2'=y2/Gamma,
    x3'=(1+s)*y3/Gamma,  x4'=y4/Gamma,

where Gamma=1+s*(y1+y3)>0.

The published model uses fixed affinity parameters. The bound below also permits them to vary between generations, including as functions of the current state, provided each remains a probability. That extension is explicitly ours; it is not attributed to the source.

The question is quantitative: can arbitrary affinity biases prevent fixation, or make it arbitrarily slow for a fixed interior initial state and fixed positive selection, in this particular model?

## Theorem

Let x(n) follow the four recursions with constant s>0 and arbitrary b1(n),b2(n) in [0,1]. Suppose r>=0 satisfies

    x2(0) <= r*x1(0),    x4(0) <= r*x3(0).

Put c=1/(1+s), so 0<c<1. Then for every n,

    x2(n) <= r*c^n*x1(n),
    x4(n) <= r*c^n*x3(n),

and consequently

    0 <= 1−q(n) <= (r*c^n)/(1+r*c^n) <= r*c^n.

In particular q(n) tends to one. If x1(0)>0 and x3(0)>0, one can take

    r=max(x2(0)/x1(0), x4(0)/x3(0)).

Thus every strictly positive initial frequency vector has an explicit global fixation bound, independent of the sequence of admissible affinity biases.

The initial-ratio condition is sufficient, not claimed necessary. It can also cover a missing genetic background when both coordinates for that background are zero.

## Proof

**The transmission stage is a valid frequency update.** It preserves the sum and the genetic marginals y1+y2=p and y3+y4=1−p. Nonnegativity follows either from the direct simplex bounds on D or from its interpretation as within-background convex mixing. Hence Gamma is at least one.

**Two coefficient identities.** Since D=(1−p)*x1−p*x3, direct expansion gives

    r*y1−y2
      = (1−b1*(1−p))*(r*x1−x2) + b1*p*(r*x3−x4),

    r*y3−y4
      = (1−b2*p)*(r*x3−x4) + b2*(1−p)*(r*x1−x2).

Every coefficient on the right is nonnegative, since 0<=p,b1,b2<=1. Therefore the inequalities x2<=r*x1 and x4<=r*x3 remain valid with x replaced by y.

**Selection contracts the bound.** Dividing by Gamma and using the factor 1+s on the B coordinates gives

    x2' <= (r/(1+s))*x1',
    x4' <= (r/(1+s))*x3'.

This uses no constancy of the affinity parameters, only their range in this generation.

Induction proves the two coordinate inequalities with r_n=r*c^n. Adding them yields

    1−q(n) <= r_n*q(n).

Rearrange to q(n)>=1/(1+r_n), which proves the sharper deficit bound. The weaker bound follows from r_n>=0 and 1+r_n>=1. Finally c^n tends to zero because 0<c<1. This proves fixation.

The ratio choice in the theorem is valid because initial x1 and x3 are positive, the other coordinates are nonnegative, and the maximum dominates both initial ratios.

## Interpretation

The affinity operation redistributes cultural frequencies between genetic backgrounds. It cannot push the worse background below their current shared lower bound on the frequency of B. Selection improves that lower bound each generation. This yields a certificate valid across arbitrary admissible changes of affinity.

This theorem is about a beneficial cultural trait under homogeneous positive selection. It does not concern the different cultural-trait-bias model in the same paper, where transmission can directly favour b. It does not prove speciation, epigenetic causation, genetic fixation of A, or a finite-population result. The result would need reanalysis under varying-sign selection, mutation, nonvertical kernels outside the given recursion, or demographic randomness.

## Prior-work and proof status

The source's affinity section studies boundary invasion/stability and rules out an interior equilibrium under a displayed parameter restriction. The present rate proof is a direct quantitative argument on its recursions and an explicitly declared adaptive-parameter extension. A bounded exact-title/affinity-bias search did not identify this rate formula; that is not a novelty certificate. Convex averaging plus selection is a familiar mechanism, and specialists may know this bound or a stronger one.

The fixed-point exclusion proof in the companion audit also covers marginally polymorphic simplex boundary points, so it is retained separately. Absence of an interior fixed point alone does not establish this convergence theorem.

An eventual publication description must distinguish this direct model refinement from the genuinely unresolved nonvertical-transmission direction in the source. All claimed Lean endpoints must start from the four update equations or the equivalent explicit step, not assume the odds invariant as a desired conclusion. The initial ratio bound is a hypothesis with a separately proved positive-coordinate witness.


The final bounded prior-art check gives a simpler structural description: transmission applies the same nonnegative two-by-two matrix to u=(x1,x3) and v=(x2,x4). Coordinatewise v<=r*u implies M*v<=r*M*u; selection then contracts r by 1/(1+s). This is standard order preservation, not new general contraction machinery. The potentially useful result is its precise source-model application, explicit parameter scope and Lean verification. See RATE-PRIOR-ART-CHECK.md for the six queries, three nearest primary leads and access limits.
