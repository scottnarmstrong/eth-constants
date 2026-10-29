/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import SATSetup

public section
namespace ETHConstants.SAT
open Levels.Gen ClauseBound.Gen GeneralPieces GeneralPieces.PartA

theorem rho_ge_seven_tenths : (7/10:ℝ) ≤ rho := by
  nlinarith [rho_sq, rho_ge]

/-- The original 0.85 bound can be tightened to 0.7 for these specific parameters. -/
theorem y_sharp (l : ℕ) : y rho 16 l ≤ 7/10 - (1/5:ℝ)/(2:ℝ)^l := by
  have hr0 : 0 < rho := by linarith [rho_ge]
  induction l with
  | zero => norm_num [y, e]
  | succ l ih =>
    have hK : (0:ℝ) < K 16 l := by rw [K_cast]; positivity
    have hp : (0:ℝ) < (2:ℝ)^l := by positivity
    have hR : (0:ℝ) < rho^(l+1) := by positivity
    have hy0 : 0 ≤ y rho 16 l := div_nonneg
      (PartAUse.e_nonneg partA hr0.le l) (by positivity)
    have hy1 : y rho 16 l ≤ 7/10 := by linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1/5) hp.le]
    have hz : zeta l = 1 / (32*(2:ℝ)^l) := by
      unfold zeta
      rw [pow_add]
      norm_num
      ring
    have hf : 3*zeta l/rho ≤ (15/112:ℝ)/(2:ℝ)^l := by
      rw [hz]
      apply (div_le_iff₀ hr0).2
      convert div_le_div_of_nonneg_right
        (show (3/32:ℝ) ≤ (15/112)*rho by nlinarith [rho_ge_seven_tenths]) hp.le using 1 <;> ring
    have hkN : 8192*(2^l)^2 ≤ K 16 l := by
      calc 8192*(2^l)^2 = 2^(13+2*l) := by
            rw [pow_add, ← pow_mul]
            norm_num only [Nat.reducePow]
            congr 2
            omega
        _ ≤ 2^(16*(l+1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ K 16 l := K_ge_pow 16 l le_rfl
    have hkR : (8192:ℝ)*((2:ℝ)^l)^2 ≤ (K 16 l:ℝ) := by exact_mod_cast hkN
    have herr : 6*(2:ℝ)^l/(K 16 l:ℝ) ≤ (1/1000:ℝ)/(2:ℝ)^l := by
      rw [div_le_div_iff₀ hK hp]
      nlinarith only [hkR, sq_nonneg ((2:ℝ)^l)]
    have hlo : (1/2:ℝ)^(l+1) ≤ rho^(l+1) := pow_le_pow_left₀ (by norm_num) rho_ge _
    have hpR : (1:ℝ) ≤ 2^(l+1)*rho^(l+1) := by
      calc (1:ℝ) = 2^(l+1)*(1/2:ℝ)^(l+1) := by rw [← mul_pow]; norm_num
        _ ≤ 2^(l+1)*rho^(l+1) := mul_le_mul_of_nonneg_left hlo (by positivity)
    have herr' : 3/(K 16 l:ℝ)/rho^(l+1) ≤ 6*(2:ℝ)^l/(K 16 l:ℝ) := by
      rw [div_div, div_le_div_iff₀ (mul_pos hK hR) hK]
      have hprod := mul_le_mul_of_nonneg_left hpR (show (0:ℝ) ≤ 3*(K 16 l:ℝ) by positivity)
      rw [pow_succ] at hprod
      nlinarith only [hprod]
    have hrec : y rho 16 (l+1) = (1+3*zeta l/rho)*y rho 16 l + 3/(K 16 l:ℝ)/rho^(l+1) := by
      simp only [y, e, pow_succ]
      field_simp
    have hmul := mul_le_mul hf hy1 hy0 (show (0:ℝ) ≤ (15/112:ℝ)/2^l by positivity)
    have hidmul : (15/112:ℝ)/2^l*(7/10) = (3/32:ℝ)/2^l := by ring
    rw [hidmul] at hmul
    have hh : y rho 16 (l+1) ≤ y rho 16 l + (3/32:ℝ)/2^l + (1/1000:ℝ)/2^l := by
      rw [hrec]
      have herr2 := herr'.trans herr
      nlinarith only [hmul, herr2]
    have hnext : (1/5:ℝ)/2^(l+1) = (1/10:ℝ)/2^l := by rw [pow_succ]; ring
    rw [hnext]
    have hid : (3/32:ℝ)/2^l+(1/1000:ℝ)/2^l+(1/10:ℝ)/2^l ≤ (1/5:ℝ)/2^l := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hp.le
    linarith only [hh, ih, hid]

theorem e_sharp (l : ℕ) : e rho 16 l ≤ (7/10:ℝ)*rho^l := by
  have hp : (0:ℝ) < rho^l := pow_pos (by linarith [rho_ge]) _
  have h : y rho 16 l ≤ (7/10:ℝ) := (y_sharp l).trans (sub_le_self _ (by positivity))
  exact (div_le_iff₀ hp).1 h

end ETHConstants.SAT
