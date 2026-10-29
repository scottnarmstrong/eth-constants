/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import SATSetup
public import SATRates
public import UniformInK.Top.ArithNat
public import ClauseBound.ParityChecks.ArithAux
import Mathlib.Data.Nat.Size

@[expose] public section
namespace ETHConstants.SAT
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
open GeneralPieces UniformInK VariableBound

/-- Spend more of the budget on sparsification: s = max 4 (floor(l/2) - 12).
The subtraction is natural-number subtraction. -/
def precision (l : ℕ) : ℕ := l / 2 - 16 + 4

def precisionProgram (u : U) : U := () :: () :: () :: () :: u.take (u.length / 2 - 16)

theorem precision_length (u : U) : (precisionProgram u).length = precision u.length := by
  have h : u.length/2-16 ≤ u.length := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  simp only [precisionProgram, List.length_cons, List.length_take, Nat.min_eq_left h, precision]

theorem precision_poly : PolyT precisionProgram := by
  unfold precisionProgram
  fun_prop

theorem rho_pow_bounds (l : ℕ) :
    1 / (2 : ℝ)^(l / 2 + 1) ≤ rho^l ∧ rho^l ≤ 1 / (2 : ℝ)^(l / 2) := by
  have hp : 0 < (2 : ℝ)^(l/2) := by positivity
  have hpar : l = 2 * (l / 2) ∨ l = 2 * (l / 2) + 1 := by omega
  rcases hpar with he | he
  · have hh : rho^l = 1 / (2 : ℝ)^(l/2) := by rw [he, pow_mul, rho_sq, div_pow]; norm_num
    rw [hh, pow_succ]
    constructor <;> (first | exact le_rfl | apply one_div_le_one_div_of_le hp; linarith)
  · have hh : rho^l = rho / (2 : ℝ)^(l/2) := by
      calc rho^l = rho^(2*(l/2)+1) := congrArg (rho^·) he
        _ = rho / (2 : ℝ)^(l/2) := by rw [pow_succ, pow_mul, rho_sq, div_pow]; ring
    rw [hh, pow_succ]
    constructor
    · rw [div_le_div_iff₀ (by positivity) hp]; nlinarith [rho_ge]
    · exact div_le_div_of_nonneg_right rho_lt.le hp.le

/-- The sparsification budget is kept separate from the recursive clique budget. -/
theorem main_small_of33 (l : ℕ) (hl : 33 ≤ l) :
    (140*3*((betaU 3 (precision l)+1 : ℕ):ℝ)+1) * e rho 16 l +
      1/(2:ℝ)^precision l < 1 := by
  have he := (partA.e_bounds l).2
  rcases eq_or_lt_of_le hl with rfl | hl
  · have hr : rho^33 ≤ (3/4:ℝ)/2^16 := by
      calc rho^33 = (rho^2)^16*rho := by ring
        _ ≤ (1/2:ℝ)^16*(3/4) := by rw [rho_sq]; exact mul_le_mul_of_nonneg_left rho_le (by positivity)
        _ = (3/4:ℝ)/2^16 := by norm_num
    norm_num [precision, betaU]
    norm_num at hr he
    linarith only [hr, he]
  · have hm : 17 ≤ l/2 := by omega
    have hs : precision l+12 = l/2 := by unfold precision; omega
    have hpoly : ∀ m : ℕ, 17 ≤ m → (17:ℝ)/20*(10080*m-77699)+4096 < 2^m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
        rw [pow_succ]
        push_cast
        have hmR : (17:ℝ) ≤ m := by exact_mod_cast hm
        nlinarith only [ih, hmR]
    have hu := (rho_pow_bounds l).2
    have he' : e rho 16 l ≤ (17/20:ℝ)/2^(l/2) := by
      calc e rho 16 l ≤ (17/20:ℝ)*rho^l := by convert he using 1; norm_num
        _ ≤ (17/20:ℝ)/2^(l/2) := by
          simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 17/20)
    have hc : (140*3*((betaU 3 (precision l)+1 : ℕ):ℝ)+1) = 10080*(l/2:ℕ)-77699 := by
      have hsR : (precision l:ℝ)+12 = (l/2:ℕ) := by exact_mod_cast hs
      unfold betaU
      push_cast
      nlinarith only [hsR]
    have ht : (1:ℝ)/2^precision l = 4096/2^(l/2) := by
      rw [← hs, pow_add]
      norm_num
      ring
    rw [hc, ht]
    have hc0 : (0:ℝ) ≤ 10080*(l/2:ℕ)-77699 := by
      have : (17:ℝ) ≤ (l/2:ℕ) := by exact_mod_cast hm
      linarith
    calc (10080*(l/2:ℕ)-77699:ℝ)*e rho 16 l+4096/2^(l/2)
        ≤ (10080*(l/2:ℕ)-77699)*((17/20:ℝ)/2^(l/2))+4096/2^(l/2) :=
          add_le_add (mul_le_mul_of_nonneg_left he' hc0) le_rfl
      _ = ((17/20:ℝ)*(10080*(l/2:ℕ)-77699)+4096)/2^(l/2) := by ring
      _ < 1 := (div_lt_one (by positivity)).2 (hpoly (l/2) hm)

/-- With the sharper recurrence estimate, level 32 already suffices. -/
theorem main_small (l : ℕ) (hl : 32 ≤ l) :
    (140*3*((betaU 3 (precision l)+1 : ℕ):ℝ)+1) * e rho 16 l +
      1/(2:ℝ)^precision l < 1 := by
  rcases eq_or_lt_of_le hl with rfl | hl
  · have he := e_sharp 32
    have hr : rho^32 = (1/2:ℝ)^16 := by
      calc rho^32 = (rho^2)^16 := by ring
        _ = (1/2:ℝ)^16 := by rw [rho_sq]
    rw [hr] at he
    norm_num at he
    norm_num [precision, betaU]
    linarith only [he]
  · exact main_small_of33 l (by omega)

/-- The exact network logarithm permits levels 28 through 31 at precision four. -/
theorem main_small_four (l : ℕ) (hl : 28 ≤ l) :
    (17929 : ℝ) * e rho 16 l + 1 / (2:ℝ)^4 < 1 := by
  have hr : rho^l ≤ rho^28 := pow_le_pow_of_le_one
    (by linarith [rho_ge]) rho_lt.le hl
  have he := (e_sharp l).trans (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 7/10))
  have hpow : rho^28 = (1/2:ℝ)^14 := by
    calc rho^28 = (rho^2)^14 := by ring
      _ = (1/2:ℝ)^14 := by rw [rho_sq]
  rw [hpow] at he
  norm_num at he ⊢
  linarith only [he]

/-- A limitation of the level-eight budget certificate, not a runtime lower bound. -/
theorem level_eight_coefficient_lt {a : ℝ} (ha : 0 ≤ a)
    (h : a * e rho 16 8 + 1 / (2:ℝ)^4 < 1) : a < 30 := by
  have he := (partA.e_bounds 8).1
  have hp : rho^8 = (1/2:ℝ)^4 := by
    calc rho^8 = (rho^2)^4 := by ring
      _ = (1/2:ℝ)^4 := by rw [rho_sq]
  rw [hp] at he
  norm_num at he h
  have hm := mul_le_mul_of_nonneg_left he ha
  nlinarith only [hm, h]

/-- A deliberately simple integer envelope for all lower order terms. -/
theorem linear_le_x (l : ℕ) (hl : 10 ≤ l) : 200*(l+1) ≤ x 16 l := by
  have h : 200*(l+1) ≤ 16*2^l := by
    induction l, hl using Nat.le_induction with
    | base => norm_num
    | succ l hl ih => rw [pow_succ]; nlinarith
  exact h.trans (by simpa [Nat.mul_comm] using PartA.x_ge_pow 16 l)

theorem beta_le (l : ℕ) : betaU 3 (precision l) ≤ 24*l+198 := by
  unfold betaU precision
  omega

theorem size_K_le (l : ℕ) : (K 16 l).size ≤ 2^(l+6) := by
  rw [K_eq, Nat.size_pow]
  have hf := PartA.x_formula 16 l
  have hx : x 16 l + 1 ≤ 64*2^l := by
    have hp : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hl : (0:ℝ) ≤ l := Nat.cast_nonneg _
    norm_num at hf
    have : (x 16 l:ℝ)+1 ≤ 64*(2:ℝ)^l := by linarith
    exact_mod_cast this
  simpa [pow_add, Nat.mul_comm] using hx

theorem W_small_nat (l : ℕ) (hl : 28 ≤ l) :
    ccD 3 1157 * WofU (betaU 3 (precision l)) (K 16 l) * 2^(l+1) ≤ K 16 l := by
  have hc : ccD 3 1157 ≤ 2^27 := by norm_num [ccD, GD]
  have hb := beta_le l
  have hbsize : betaU 3 (precision l)+3 ≤ 2^(l+8) := by
    have h1 : l+1 ≤ 2^l := Nat.lt_two_pow_self
    have h2 : 256*(l+1) ≤ 256*2^l := Nat.mul_le_mul_left _ h1
    rw [pow_add]
    norm_num
    omega
  have hW : WofU (betaU 3 (precision l)) (K 16 l) ≤ 2^(27*l+220) := by
    unfold WofU
    calc (betaU 3 (precision l)+3)^2 * 2^betaU 3 (precision l) * (K 16 l).size
        ≤ (2^(l+8))^2 * 2^(24*l+198) * 2^(l+6) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hbsize 2)
            (Nat.pow_le_pow_right (by norm_num) hb)) (size_K_le l)
      _ = 2^(27*l+220) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  calc ccD 3 1157 * WofU (betaU 3 (precision l)) (K 16 l) * 2^(l+1)
      ≤ 2^27 * 2^(27*l+220) * 2^(l+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hc hW)
    _ = 2^(28*l+248) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2^(x 16 l) := Nat.pow_le_pow_right (by norm_num)
      (by have := linear_le_x l (by omega); omega)
    _ = K 16 l := (K_eq 16 l).symm

theorem W_small (l : ℕ) (hl : 28 ≤ l) :
    (WofU (betaU 3 (precision l)) (K 16 l) : ℝ) ≤
      (1 / (ccD 3 1157:ℝ)) * (K 16 l) * e rho 16 l := by
  have h := W_small_nat l hl
  have hr : (ccD 3 1157:ℝ) * (WofU (betaU 3 (precision l)) (K 16 l):ℝ) *
      (2:ℝ)^(l+1) ≤ (K 16 l:ℝ) := by exact_mod_cast h
  have hp : 0 < (2:ℝ)^(l+1) := by positivity
  have hc : (0:ℝ) < ccD 3 1157 := by norm_num [ccD, GD]
  have hdiv : (ccD 3 1157:ℝ) * (WofU (betaU 3 (precision l)) (K 16 l):ℝ) ≤
      (K 16 l:ℝ) / (2:ℝ)^(l+1) := (le_div_iff₀ hp).2 hr
  have he := PartAUse.inv_two_pow_le_e partA rho_ge l
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (K 16 l))
  have hh : (ccD 3 1157:ℝ) * (WofU (betaU 3 (precision l)) (K 16 l):ℝ) ≤
      (K 16 l:ℝ) * e rho 16 l := hdiv.trans (by simpa only [mul_one_div] using hmul)
  have hh' : (WofU (betaU 3 (precision l)) (K 16 l):ℝ) ≤
      (K 16 l:ℝ)*e rho 16 l / (ccD 3 1157:ℝ) :=
    (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hh)
  convert hh' using 1; ring

theorem delta_six_le_K (l : ℕ) (hl : 28 ≤ l) :
    (2^betaU 3 (precision l))^6 ≤ K 16 l := by
  rw [← pow_mul, K_eq]
  apply Nat.pow_le_pow_right (by norm_num)
  have hb := beta_le l
  have hx := linear_le_x l (by omega)
  omega

end ETHConstants.SAT
