# Individual finite-edit additive constants: exact remaining target

## Status

The general individual-optimum refinement remains open in this repository. The existing Lean theorems prove the sharp constant uniform over all edits below a cutoff, exact maxima for each chosen start, and the equality test for the universal bound. They do not yet give a certified finite algorithm for the smallest additive constant of each fixed edited target.

This note preserves that stronger target and develops a concrete finite-reduction route. The reduction below depends on one explicitly stated branch-separation lemma which is not proved here. No new Lean module or verification receipt is claimed for this investigation.

## The target, and what already follows

Fix a target s agreeing with Thue-Morse t at every index at least m. Write L_s(v) for its actual attained maximum matching length, using FiniteEditExact.height.

The individual optimum is the largest integer residual

```math
B_s = \max_{v\ge 1}\bigl(3L_s(v)-8v\bigr).
```

Equivalently, B_s is the smallest integer B such that every positive start satisfies the additive bound with B. The checked universal theorem supplies B_s at most 8m minus one. It does not assert that every individual target attains that universal value.

A maximum does exist and is attained: the residuals form a nonempty set of integers bounded above. This is an existence argument, not an effective bound on which starting vertices must be examined.

In fact, a direct mathematical deduction from the existing shifted extremal family improves the elementary transport lower bound to

```math
-1 \le B_s \le 8m-1.
```

Here is that deduction. Take a dyadic q large enough that q exceeds m, and put a equal to 3q minus one. The checked phase-extremal family gives a matching suffix, beginning at time m and vertex a+m, that lasts to total length 8q minus three. Run the first m edited target labels backwards from that vertex. At each vertex there is exactly one incoming edge with the required label, and each backwards step subtracts one or two. The resulting start is a-p for an integer p between zero and m. Choosing q large keeps the entire backwards segment in the graph. The whole edited path therefore has residual 8p minus one.

The universal upper bound then makes the set of residual values at least minus one a finite, nonempty set; its largest value is attained. Determining which values occur over all starts still requires a global argument.

## A concrete two-value dyadic tail

For each dyadic q sufficiently large, define the backwards calculation explicitly:

```math
w_m=3q+m-1,
\qquad
w_k=
\begin{cases}
w_{k+1}-1,&t(w_{k+1})=s(k),\\
w_{k+1}-2,&t(w_{k+1})\ne s(k),
\end{cases}
\quad k=m-1,\ldots,0.
```

All vertices queried are beyond the edited graph-row region when q exceeds 2m+2, so the original row is exactly t. Put

```math
p_n=3\cdot2^n-1-w_0,
\qquad 0\le p_n\le m.
```

This gives an actual edited matching path of length 8 times 2 to the n minus three, starting at w_0, with residual 8p_n minus one. Its proof can be assembled from backward_prefix, the phase-extremal suffix, and FiniteEditExact.prefix_decomposition.

For all sufficiently large n, the local Thue-Morse window used by this finite backwards calculation depends only on the parity of n. The relevant identities, for q equal to 2 to the n, are

```math
t(3q+j)=t(j) \quad (0\le j<q),
\qquad
t(3q-r)=1\mathbin{\mathrm{xor}}(n\bmod2)
                 \mathbin{\mathrm{xor}}t(r-1)
\quad (1\le r<q).
```

Consequently p_n has at most two eventual values. They can be obtained by choosing any sufficiently large q and its double and performing two finite backwards traces. Call their maximum P. The dyadic witnesses give the explicit attained lower bound B_s at least 8P minus one.

This finite pair is not yet proved to account for all large starting vertices.

## The exact missing branch-separation lemma

A useful lemma would state:

> If q is a power of two, twice m is at most q, and a matching path for the original target t begins at 3q minus one and has length at least 4q, then its vertex at time m is exactly 3q+m minus one.

This says that a sufficiently long match from the extremal start must use the all-one-step initial segment through that time. It is stronger than the existing theorem locating starts and lengths of exact equality. The latter does not, by itself, identify the initial segment of every nearly maximal path.

The lemma is a concrete statement about the already defined MatchesPrefix and path evaluation, with no new biological assumptions. A formal proof could analyze the competing branches using the explicit dyadic boundary trajectories in FullHeight. It must rule out all noncanonical branches, rather than checking only the path chosen for an equality witness.

A second, simpler lemma follows by cases from the existing complete FullHeight table:

> For every positive u, either u is of the form 3 times a power of two minus one, or the unedited maximum L_t(u) is at most u+1.

The exceptional even case u=2 is itself an extremal dyadic start. Other large heights in the table have a sufficient gap from the coefficient 8/3. This deduction has been checked algebraically in this investigation but has not been added as a new Lean theorem.

## Why those lemmas give a finite algorithm

Assume the branch-separation lemma and the displayed off-extremal gap have been proved. Set R equal to 7m+8. Compute:

1. The two eventual backwards displacements, using sufficiently large consecutive dyadic scales.
2. Every exact residual from start 1 through R, using the existing finite-frontier maximum algorithm.

The candidate answer is

```math
\max\left(
 8p_{\mathrm{even}}-1,\;
 8p_{\mathrm{odd}}-1,\;
 \max_{1\le v\le7m+8}(3L_s(v)-8v)
\right).
```

Every candidate value is attained or comes from an attained path, so it is a lower bound for B_s. To prove it is an upper bound, suppose a start v greater than R improved it. The candidate is at least minus one, so the improving integer residual is nonnegative.

Apply the checked finite-edit transport to a longest matching path from v. It produces an original Thue-Morse path of the same length, starting at some a within distance m of v, and agrees with the edited path at time m.

If a is not an extremal start, the off-extremal gap bounds the length by a+1, which makes the edited residual at most 3m+3 minus 5v, a negative number. This contradicts improvement. Thus a is 3q minus one.

The large-start threshold forces q to exceed 2m+2. The nonnegative residual also makes the path length at least 4q. Branch separation now forces its time-m vertex to be 3q+m minus one. Incoming edges with a specified label have unique parents, so the edited path's start must be exactly the finite backwards start used above. Its residual is at most the corresponding value 8p_n minus one, contradicting improvement again.

This gives an explicit finite global reduction once the stated branch-separation lemma and its algebraic supporting lemmas are checked. It does not require a full joint phase/start digit recurrence.

## Bounded discovery checks, not proofs

A small boundary-trajectory calculation examined every cutoff m from one through q/2, for dyadic q from 2 through 256. For every cutoff, it tested all reachable cutoff vertices other than 3q+m minus one. None continued to total length 4q.

For q equal to 4, 8, 16, 32, 64, 128 and 256, the longest observed noncanonical continuation had total length 5q/2 minus one. For q=2, it had total length three. These observations motivate the branch-separation lemma; they do not prove it.

A separate bounded scan over all edited prefixes of lengths zero through seven, and starts one through 180, found no residual exceeding the two eventual backwards-trace values. That suggests the finite exceptional-start term might eventually be removable, but no such simplification should be stated as a theorem.

## Exact one-bit subcase

The case m=1 is an immediate mathematical corollary of existing checked endpoints:

- If s(0) is false, agreement from one implies s=t. The unedited sharp theorem gives B_s equal to minus one.
- If s(0) is true, s equals sharpEdit 1 1. The existing sharpEdit_equality witness has start four and maximum length thirteen, giving residual seven. The universal bound gives B_s at most seven, hence equality.

No new dedicated Lean endpoint was compiled for this corollary. It is an exact subcase, not a replacement for the general individual-optimum question.

## Other refinements that must remain visible

| Original refinement | Current completed result | Exact remaining target |
| --- | --- | --- |
| Joint phase/index digit description | Exact maxima are computable for every phase and start; phase-zero has a certified finite digit recurrence. | A finite digit recurrence or closed form treating phase and starting index jointly, with its exact domain and any claimed complexity bound. |
| Optimal fixed-gender root count | The directed-line construction attains the optimal child cap two and has exactly three roots. | Whether three roots are necessary under the same avoidance and population requirements, or whether two roots can attain those requirements. The exact child-cap threshold does not settle this. |
| Crossing widths above the minimum | The minimal-width tail is exactly the kth power of a ray; finite-port encoding is available. | Structural classification at larger widths, including the binary width-four regime and its label-language behavior. The encoding alone is not a classification. |
| Natural or published cellular automata | The crafted three-state rule has a strict comparison between the specified static and stateful certificate classes. | A verified improvement for a natural binary or published rule, with its actual transition rule, evolution, certificate classes, and comparison against existing bounds. The synthetic example does not answer that target. |

The ledger should retain these as unfinished refinements. The general finite-edit algorithm should move to proved status only after the global reduction, its source-to-height bridge, and the resulting executable finite procedure have actually passed formal checking.