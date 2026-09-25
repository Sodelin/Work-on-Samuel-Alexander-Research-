# What a finite ancestry graph determines about infinite specieslike status

The formal input is an actual finite interval genome ARG, not a DNA sequence dataset. `FiniteGenomeIdentifiability` gives an explicit recovery obstruction for Alexander's whole-population specieslike predicate in the class of abstract topology-compatible infinite completions.

`Compatible G E` requires an injective genome-node encoding into a population graph, literal real-date and natural-date biosphere conditions, finitely many roots, whole-population weak connectivity, exact preservation and reflection of all old edges, and exact preservation and reflection of all old ancestry. The existing opposite-completion theorem supplies two such completions of each finite gARG: one whole graph is specieslike, while the other is not.

Three selected endpoints make the implication explicit:

- `opposite_compatible_completions`: both specieslike outcomes are compatible with the same finite gARG.
- `no_exact_specieslike_verdict`: no proposition chosen solely from that fixed finite input is correct for every compatible completion.
- `no_exact_specieslike_decoder`: in particular, an arbitrary proposed decoder of finite gARGs cannot have that universal guarantee.

This is a direct corollary of the checked finite-history completion theorem, with no separate novelty claim. It clarifies why ancestry-preserving maps and finite graph formalization do not by themselves establish a positive biological species classifier.

The compatibility condition is about the raw graph topology and original-node ancestry. It does not infer a biological genome-owner map, extend genomic labels or DNA observations into the future, specify a coalescent probability model, or identify every biological species concept with whole-population specieslikeness. Statistical identifiability from a model's probability distribution and reliable finite-sample classification are different questions and are not contradicted by this result.

The coordinator individually compiled the three endpoints with Lean 4.33.1 and only the permitted standard axioms. This copy is registered for the implementation checkout's fresh aggregate audit; the exact source hash and current aggregate result belong to `verification/real-audit.json`.

The current integrated source inventory is in [the core receipt](../verification/formal-audit.json) and [the mathlib receipt](../verification/real-audit.json). All selected endpoints use only the permitted standard axioms.
