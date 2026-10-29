/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ExplicitRecursion

/-! A fully numerical example in the counted, table-query model.
This is a clique tensor-network bound, not a Turing-machine SAT crossover. -/

public section

namespace ETHConstants.FiniteBound
open Real Levels.Gen

theorem first_level : K 16 1 = 2 ^ 64 := by norm_num [K]

theorem first_exponent : e (1 / √2) 16 1 ≤ 401 / 1000 := by
  have hroot : (7071 / 5000 : ℝ) ≤ √2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hr : 1 / √(2 : ℝ) ≤ 5000 / 7071 := by
    calc 1 / √(2 : ℝ) ≤ 1 / (7071 / 5000) :=
      one_div_le_one_div_of_le (by norm_num) hroot
      _ = _ := by norm_num
  norm_num [e, zeta, K]
  rw [one_div] at hr
  linarith

/-- At K = 2^64 and λ = B = 2^27, the checked count is at most
2^{(9/20) K² λ}. The polynomial overhead with exponent 61515 is included. -/
theorem numerical_bound :
    CliqueLevels.bound (e (1 / √2) 16 1) (K 16 1) 61515 (2 ^ 27) (2 ^ 27) ≤
      (2 : ℝ) ^ ((9 / 20) * (K 16 1 : ℝ) ^ 2 * 2 ^ 27) := by
  have hb : (K 16 1 : ℝ) * ((2 ^ 27 : ℕ) + (2 ^ 27 : ℕ)) = (2 : ℝ) ^ 92 := by
    rw [first_level]
    norm_num
  have hc : e (1 / √2) 16 1 * (2 : ℝ) ^ 27 + 92 * 61515 ≤ (9 / 20) * 2 ^ 27 := by
    have := first_exponent
    norm_num at *
    linarith
  calc
    CliqueLevels.bound (e (1 / √2) 16 1) (K 16 1) 61515 (2 ^ 27) (2 ^ 27) =
        (2 : ℝ) ^ ((e (1 / √2) 16 1 * 2 ^ 27 + 92 * 61515) * (K 16 1 : ℝ) ^ 2) := by
      unfold CliqueLevels.bound
      rw [hb, ← pow_mul,
        ← Real.rpow_natCast (2 : ℝ) (92 * (61515 * K 16 1 ^ 2)),
        ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ ((9 / 20) * (K 16 1 : ℝ) ^ 2 * 2 ^ 27) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := mul_le_mul_of_nonneg_right hc (sq_nonneg (K 16 1 : ℝ))
      nlinarith only [h]

/-- The exponent is strictly smaller than exhaustive enumeration of all edge labels. -/
theorem beats_enumeration :
    (9 / 20 : ℝ) * (K 16 1 : ℝ) ^ 2 * 2 ^ 27 <
      (((K 16 1).choose 2 * 2 ^ 27 : ℕ) : ℝ) := by
  rw [first_level]
  norm_num [Nat.choose_two_right]

open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed in
/-- The concrete machine returns the correct value within the numerical bound,
for every valid family of tables at these parameters. -/
theorem finite_run (W : ℕ → List Bool → ℤ)
    (hW : ∀ w < K 16 1, ∀ z ∈ words ((K 16 1 - 1) * 2 ^ 27),
      |W w z| < 2 ^ (2 ^ 27)) :
    ∃ T S : ℕ,
      (ExplicitCost.cliqueMachine 193 16 ExplicitRecursion.shortAlgorithm).Within
        (tables (K 16 1) (2 ^ 27) W) QueryMachine.unitCost
        (unary 1, unary (2 ^ 27), unary (2 ^ 27)) T S
        (clique (K 16 1) (2 ^ 27) fun w => W w.val).value ∧
      (T : ℝ) ≤ (2 : ℝ) ^ ((9 / 20) * (K 16 1 : ℝ) ^ 2 * 2 ^ 27) ∧
      (S : ℝ) ≤ (2 : ℝ) ^ ((9 / 20) * (K 16 1 : ℝ) ^ 2 * 2 ^ 27) := by
  obtain ⟨T, S, hrun, hT, hS⟩ := ExplicitRecursion.solves.2
    1 (2 ^ 27) (2 ^ 27) W (by norm_num) (by norm_num) hW
  exact ⟨T, S, hrun, hT.trans numerical_bound, hS.trans numerical_bound⟩

end ETHConstants.FiniteBound
