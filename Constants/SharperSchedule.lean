/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LevelsStatement
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A sharper bound for the exact published schedule: the exponent 10 in
Theorem A(a) can be replaced by 4. This does not change the algorithm or prove
an improved end-to-end runtime. It is kept separate from the upstream proof. -/

public section

namespace ETHConstants

open Levels.Gen

/-- The multiplier used to form the next grid never exceeds the current K. -/
theorem grid_multiplier_le (x₀ l : ℕ) (hx : 1 ≤ x₀) :
    2 ^ (3 * l + x₀) ≤ K x₀ l := by
  induction l with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, K, le_refl]
  | succ l ih =>
    calc
      2 ^ (3 * (l + 1) + x₀) ≤ 2 ^ (4 * (3 * l + x₀)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = (2 ^ (3 * l + x₀) * 2 ^ (3 * l + x₀)) ^ 2 := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      _ ≤ (2 ^ (3 * l + x₀) * K x₀ l) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ih) 2
      _ = K x₀ (l + 1) := rfl

/-- The exact schedule has K_(l+1) ≤ K_l^4, strengthening the published ^10. -/
theorem next_level_le_fourth_power (x₀ l : ℕ) (hx : 1 ≤ x₀) :
    K x₀ (l + 1) ≤ K x₀ l ^ 4 := by
  calc
    K x₀ (l + 1) = (2 ^ (3 * l + x₀) * K x₀ l) ^ 2 := rfl
    _ ≤ (K x₀ l * K x₀ l) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (grid_multiplier_le x₀ l hx)) 2
    _ = K x₀ l ^ 4 := by ring

/-- Equality at the first step: 4 is the best uniform exponent for this schedule. -/
theorem first_level_eq_fourth_power (x₀ : ℕ) : K x₀ 1 = K x₀ 0 ^ 4 := by
  simp only [K, Nat.mul_zero, Nat.zero_add]
  ring

/-- With the published level cutoff, maximality now gives m < K_l^36,
where the paper's ^10 bound only gives m < K_l^90. -/
theorem input_lt_level_pow_thirty_six (x₀ l m : ℕ) (hx : 1 ≤ x₀)
    (hm : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 36 := by
  calc
    m < K x₀ (l + 1) ^ 9 := hm
    _ ≤ (K x₀ l ^ 4) ^ 9 :=
      Nat.pow_le_pow_left (next_level_le_fourth_power x₀ l hx) 9
    _ = K x₀ l ^ 36 := by rw [← pow_mul]

end ETHConstants
