# First hitting times, coefficient optimality, and finite repetitions

`SharpCorollaries.lean` proves the complete first-baseline-hit relation for
the actual Thue–Morse boundary trajectories. With $`q=2^n`$, the first hit is
zero from start zero, two from starts one and two, and $`8q-2`$ for every start
in $`[3q,6q-1]`$. The proof sandwiches each trajectory between the checked lower
and upper dyadic trajectories. Persistence of a baseline hit excludes all
earlier times. `firstHit_iff` includes all starts and all candidate times;
it is not merely an upper bound on some chosen hitting time.

The same module proves `no_smaller_rational_coefficient`: if natural $`a,b,c`$
satisfy $`3a<8b`$, some actual matching maximum obeys $`a\cdot v+c<b\cdot \ell`$.
The hypothesis already forces $`b>0`$. Arbitrarily large checked equality
starts supply the witness. This is a rational-coefficient form; the optional
`real/RealBridges.lean` project separately states the literal real-coefficient
version, governed by its own build and audit receipt.

`QuantitativeAvoidance.lean` supplies an explicit lower-bound tool in the
original target-dependent graph. If an initial segment obeys
$`s(k+p)=s(k)`$ for $`k<\ell`$, taking two-step edges from $`2p-1`$ yields a match
of $`\ell`$ edges. The row-odd formula verifies every actual edge and retains
the missing $`0 \to 1`$ convention. Fully periodic targets give an infinite
two-step path. Neither endpoint assumes that an aperiodic sequence has any
particular repeated prefix.

These are deductions from the source construction and the checked sharp
theorem. The coefficient and first-hit corollaries were already written in
the sharp proof note before this separate formalization. They are not
additional literature-priority claims.

Reproduction from the repository root:

```sh
lake build SamuelAlexanderResearch.SharpCorollaries SamuelAlexanderResearch.QuantitativeAvoidance
python checks/audit_lean.py --output verification/formal-audit.json
```

The integrated manifest registers the endpoint names and source hashes. The
optional real project has its own pinned Mathlib dependency and audit.
