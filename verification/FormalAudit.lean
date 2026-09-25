import SamuelAlexanderResearch

/-!
The exported endpoint manifest for checks/audit_lean.py.
Only propext, Classical.choice, and Quot.sound are permitted dependencies.
Formalization scope and mathematical premise review live in FORMALIZATION.md.
The conditional classification endpoint below remains conditional even though
its proof has no unexpected axioms: its positive theorem is a parameter.
-/

#print axioms PopulationDegree.offspring_threshold
#print axioms PopulationDegree.binary_vertex_gender_balance

#print axioms PopulationCounting.double_count
#print axioms PopulationCounting.nonroot_indegree
#print axioms PopulationCounting.offspring_edge_bound
#print axioms PopulationCounting.offspring_threshold
#print axioms PopulationCounting.strict_offspring_size_bound
#print axioms PopulationCounting.gender_double_count
#print axioms PopulationCounting.gender_edge_bound
#print axioms PopulationCounting.binary_vertex_gender_abs_balance
#print axioms PopulationCounting.ordered_prefix_closed
#print axioms PopulationCounting.prefix_offspring_threshold
#print axioms PopulationCounting.critical_degree_conservation
#print axioms PopulationCounting.critical_degree_budget
#print axioms PopulationCounting.prefix_binary_gender_balance
#print axioms PopulationCounting.infinite_subcritical_impossible
#print axioms PopulationCounting.no_infinite_subcritical_population

#print axioms BinaryAvoidance.decreasing_nat_stabilizes
#print axioms BinaryAvoidance.matching_implies_eventuallyPeriodic
#print axioms BinaryAvoidance.aperiodic_target_avoided

#print axioms SpeciesBridge.finiteSupport_iff_bounded
#print axioms SpeciesBridge.psDescendant_iff
#print axioms SpeciesBridge.psSubset_iap
#print axioms SpeciesBridge.psSubset_specieslike_iff
#print axioms SpeciesBridge.psWhole_bridge
#print axioms SpeciesBridge.psEvery_vertex_in_maximal_cluster

#print axioms BinaryPopulation.forget_edge_eq
#print axioms BinaryPopulation.edge_unique_labels
#print axioms BinaryPopulation.incoming_each_label
#print axioms BinaryPopulation.two_distinct_parents
#print axioms BinaryPopulation.edge_is_binaryNatPopulation
#print axioms BinaryPopulation.explicit_specieslike_avoider
#print axioms BinaryPopulation.aperiodic_specieslike_counterexample
#print axioms BinaryPopulation.specieslike_unavoidable_implies_eventuallyPeriodic
#print axioms BinaryPopulation.specieslike_classification_of_positive

#print axioms SpeciesCones.c0_iff
#print axioms SpeciesCones.c1_iff
#print axioms SpeciesCones.cone_fourAxioms
#print axioms SpeciesCones.cone_specieslike
#print axioms SpeciesCones.maximalFourAxioms_iff
#print axioms SpeciesCones.c0_ne_c1
#print axioms SpeciesCones.every_vertex_in_maximal_four_cluster

#print axioms RootObstruction.root_zero
#print axioms RootObstruction.root_one
#print axioms RootObstruction.descendant_strict
#print axioms RootObstruction.population_not_commonAncestor
#print axioms RootObstruction.population_root_obstruction

#print axioms StaticMixing.weightedSum_constant
#print axioms StaticMixing.intersection_subset_weightedMix
#print axioms StaticMixing.intersection_subset_midpointMix
#print axioms StaticMixing.strict_midpoint_example

#print axioms SamuelAlexanderResearch.ThueMorseBound.interval_step
#print axioms SamuelAlexanderResearch.ThueMorseBound.reachable_iff_interval
#print axioms SamuelAlexanderResearch.ThueMorseBound.coalescence_persists
#print axioms SamuelAlexanderResearch.ThueMorseBound.nonempty_iff_separated
#print axioms SamuelAlexanderResearch.ThueMorseBound.extinct_iff_coalesced
#print axioms SamuelAlexanderResearch.ThueMorseBound.maximum_length_iff

#print axioms ThueMorseBits.t_zero
#print axioms ThueMorseBits.t_double
#print axioms ThueMorseBits.t_double_add_one
#print axioms ThueMorseBits.t_dyadic_block
#print axioms ThueMorseBits.t_power_sub_three
#print axioms ThueMorseBits.t_power_sub_two
#print axioms ThueMorseBits.t_twice_power_sub_four
#print axioms ThueMorseBits.t_ten_pow_add_one

#print axioms SharpThueMorse.baseline
#print axioms SharpThueMorse.upper_join
#print axioms SharpThueMorse.descent_block
#print axioms SharpThueMorse.common_descent
#print axioms SharpThueMorse.upper_coalescence
#print axioms SharpThueMorse.five_run_join
#print axioms SharpThueMorse.lower_join
#print axioms SharpThueMorse.sharp_path_bound
#print axioms SharpThueMorse.sharp_maximum_exists
#print axioms SharpThueMorse.sharp_equality_family
#print axioms SharpThueMorse.binary_row_eq
#print axioms SharpThueMorse.binary_edge_iff
#print axioms SharpThueMorse.binary_prefix_reachable
#print axioms SharpThueMorse.binary_path_prefix_bound
#print axioms SharpThueMorse.sharp_equality_indices
