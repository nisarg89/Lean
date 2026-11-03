import FairDivision.BF.Certificate

/-!
# Balanced Fair Division endpoint axiom audit

Prints the transitive axioms of all 47 released endpoints.
`lean/scripts/check_axioms.py` checks the output against the permitted axioms.
-/

-- Sections 3–5: every theorem exported by the principal reader facade.
#print axioms FairDivision.BF.MainTheorems.identical_prime_power_common_threshold
#print axioms FairDivision.BF.MainTheorems.identical_prime_power_ef11
#print axioms FairDivision.BF.MainTheorems.identical_common_threshold
#print axioms FairDivision.BF.MainTheorems.identical_ef11
#print axioms FairDivision.BF.MainTheorems.heterogeneous_prime_power_ef11
#print axioms FairDivision.BF.MainTheorems.heterogeneous_one_ef11
#print axioms FairDivision.BF.MainTheorems.heterogeneous_one_or_prime_power_ef11

-- Stable existence-only aliases imported by Certificate.
#print axioms FairDivision.BF.exists_balanced_ef11_identical_prime_power
#print axioms FairDivision.BF.exists_balanced_ef11_identical
#print axioms FairDivision.BF.exists_balanced_ef11_heterogeneous_prime_power

-- Ordinary EF1 restoration and its exact item-witness interpretation.
#print axioms FairDivision.BF.goodsEF1For_iff_actual_item_of_envy
#print axioms FairDivision.BF.choresEF1For_iff_actual_item_of_envy
#print axioms FairDivision.BF.heterogeneous_primePower_exists_balanced_ordinaryEF1
#print axioms FairDivision.BF.identical_exists_balanced_goodsEF1
#print axioms FairDivision.BF.identical_exists_balanced_choresEF1

-- `thm:swap` / `sec:exchange`: both clauses of the sharp swap threshold.
#print axioms FairDivision.BF.sharp_swap_threshold

-- The two replacement-fairness propositions, in both valuation regimes.
#print axioms FairDivision.BF.ReplacementFairness.identical_exists_enviedReplacement
#print axioms FairDivision.BF.ReplacementFairness.primePower_exists_enviedReplacement
#print axioms FairDivision.BF.ReplacementFairness.identical_exists_ownReplacement
#print axioms FairDivision.BF.ReplacementFairness.primePower_exists_ownReplacement

-- Full equal capacities, including capacity zero, and feasible subsets.
#print axioms FairDivision.BF.Applications.feasibleGoodsEF1_iff
#print axioms FairDivision.BF.Applications.primePower_exists_full_capacity_goodsEF1
#print axioms FairDivision.BF.Applications.identical_exists_full_capacity_goodsEF1

-- Sharp graph-density theorem, with N and k fixed before the sharp example.
#print axioms FairDivision.BF.Applications.exists_balanced_density_partition_cases
#print axioms FairDivision.BF.Applications.exists_balanced_density_partition
#print axioms FairDivision.BF.Applications.sharp_balanced_density_bound
#print axioms FairDivision.BF.Applications.sharp_balanced_density_partitions

-- Nonlinear discrepancy and its literal sharp examples (via Coverage).
#print axioms FairDivision.BF.Applications.exists_balanced_nonlinear_discrepancy
#print axioms FairDivision.BF.Applications.exists_balanced_monotone_discrepancy
#print axioms FairDivision.BF.Applications.exists_balanced_antitone_discrepancy
#print axioms FairDivision.BF.Applications.nonlinear_constant_two_sharp
#print axioms FairDivision.BF.Applications.monotone_constant_one_sharp

-- Sparse coverage, simultaneous cardinality, and family-model comparison.
#print axioms FairDivision.BF.Applications.exists_balanced_sparse_coverage
#print axioms FairDivision.BF.Applications.exists_coverage_cardinality_pair
#print axioms FairDivision.BF.Applications.coverage_constant_sharp
#print axioms FairDivision.BF.Applications.coverage_sharp_equal_parts
#print axioms FairDivision.BF.Applications.coverage_hit_set_representation
#print axioms FairDivision.BF.Applications.cardinality_hit_set_representation
#print axioms FairDivision.BF.Applications.coverage_cardinality_sparsity

-- Equal-parameter extraction and its induced-graph applications.
#print axioms FairDivision.BF.Applications.exists_disjoint_equal_parameters
#print axioms FairDivision.BF.Applications.unitDeletion_distinct_values_le
#print axioms FairDivision.BF.Applications.caro_yuster_generic_comparison
#print axioms FairDivision.BF.Applications.exists_disjoint_equal_clique_numbers
#print axioms FairDivision.BF.Applications.exists_disjoint_equal_independence_numbers
#print axioms FairDivision.BF.Applications.exists_disjoint_equal_chromatic_numbers
#print axioms FairDivision.BF.Applications.graphParameter_values_le
#print axioms FairDivision.BF.Applications.graphParameter_caro_yuster_comparison
