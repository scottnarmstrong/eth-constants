module
import SharperSchedule
import PartitionEncoding
import ExplicitPieces
import ExplicitRecursion
import FiniteBound
import SATSetup
import SATRates
import SATNeed
import SATNumerics
import SATFallback
import SharperPartitions

#print axioms ETHConstants.grid_multiplier_le
#print axioms ETHConstants.next_level_le_fourth_power
#print axioms ETHConstants.first_level_eq_fourth_power
#print axioms ETHConstants.input_lt_level_pow_thirty_six
#print axioms ETHConstants.PartitionEncoding.two_pow_le_partitions
#print axioms ETHConstants.PartitionEncoding.hOf_le
#print axioms ETHConstants.ExplicitPieces.partition_bounds
#print axioms ETHConstants.ExplicitPieces.caps_le
#print axioms ETHConstants.ExplicitPieces.cst
#print axioms ETHConstants.ExplicitPieces.par
#print axioms ETHConstants.ExplicitPieces.isPieces
#print axioms ETHConstants.ExplicitRecursion.setting
#print axioms ETHConstants.ExplicitRecursion.recursionConstant
#print axioms ETHConstants.ExplicitRecursion.solves
#print axioms ETHConstants.FiniteBound.first_exponent
#print axioms ETHConstants.FiniteBound.numerical_bound
#print axioms ETHConstants.FiniteBound.beats_enumeration
#print axioms ETHConstants.FiniteBound.finite_run
#print axioms ETHConstants.SAT.parameters
#print axioms ETHConstants.SAT.rateConstant
#print axioms ETHConstants.SAT.solver_poly
#print axioms ETHConstants.SAT.solver_rate
#print axioms ETHConstants.SAT.y_sharp
#print axioms ETHConstants.SAT.e_sharp
#print axioms ETHConstants.SATNeed.needD_le_exact
#print axioms ETHConstants.SAT.precision_poly
#print axioms ETHConstants.SAT.main_small
#print axioms ETHConstants.SAT.W_small
#print axioms ETHConstants.SAT.delta_six_le_K
#print axioms ETHConstants.SAT.cutoff_ge
#print axioms ETHConstants.SAT.chosen_plan_lt
#print axioms ETHConstants.SAT.budget_lt
#print axioms ETHConstants.SAT.no_fallback
#print axioms ETHConstants.SAT.algorithm_correct
#print axioms ETHConstants.SAT.algorithm_poly
#print axioms ETHConstants.Partition.third_moment_exp_le
#print axioms ETHConstants.Partition.partition_lower_bound
#print axioms ETHConstants.Partition.explicit_partition_lower_bound

#print axioms ETHConstants.SATNeed.needD_le_of_ub
#print axioms ETHConstants.SATNeed.ubD_precision_four_le
#print axioms ETHConstants.SAT.main_small_four
#print axioms ETHConstants.SAT.level_eight_coefficient_lt
#print axioms ETHConstants.SAT.selected_at_target
