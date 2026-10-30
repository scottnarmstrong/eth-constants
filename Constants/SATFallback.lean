/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import SATNumerics
public import SATNeed
public import VariableBound.Net.Main
public import RecursionWithPieces.Main
public import SparsifyThenCount.Main
public import StepSparsify.CalServes
public import ClauseBound.Alg.Decode
import all VariableBound.Top.ArithTop
import ClauseBound.Alg.TopArith
import all ClauseBound.TopN.Arith

@[expose] public section
namespace ETHConstants.SAT
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
open GeneralPieces UniformInK VariableBound ClauseBound.ParityChecks ClauseBound.TopN
open SparsifyThenCount ClauseBound.Alg.TopArith
open ClauseBound.TopN.Arith

/-- The padding exponent is strictly below n throughout every interval from level 18 onward. -/
theorem need_lt (l n : ℕ) (hl : 18 ≤ l) (hn : K 16 l ^ 17 ≤ n)
    (hn' : n < K 16 (l+1)^17) :
    needD solver 3 (idx pieces 16 l) n (precision l) < n := by
  have hK : 2 ≤ K 16 l := PartAUse.two_le_K partA l
  have hKn : K 16 l ≤ n := (Nat.le_self_pow (by norm_num) _).trans hn
  have hlt : n < K 16 l^(17*1157) := by
    have hle : K 16 (l+1) ≤ K 16 l^1157 :=
      (next_level_le_fourth_power 16 l (by norm_num)).trans
        (Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 1157))
    have hh := hn'.trans_le (Nat.pow_le_pow_left hle 17)
    simpa only [← pow_mul, Nat.mul_comm] using hh
  have hD : 2^betaU 3 (precision l) ≤ n+1 :=
    ((Nat.le_self_pow (by norm_num) _).trans (delta_six_le_K l hl)).trans (by omega)
  have he0 : 0 < e rho 16 l := lt_of_lt_of_le (by positivity) (partA.e_bounds l).1
  have he1 : e rho 16 l ≤ 1 := PartAUse.e_le_one partA (by linarith [rho_ge]) rho_lt.le l
  have hN : (needD solver 3 (idx pieces 16 l) n (precision l):ℝ) < n := by
    by_cases h32 : 32 ≤ l
    · have hN := SATNeed.needD_le_exact (stUbD Net.Main.bounds) (stArgD Net.Main.bounds)
        (stLowerD Net.Main.bounds) stBetaU solver (idx pieces 16 l)
        (C₀ := 1157) (k := 3) (n := n) (s := precision l)
        (A₁ := 1/(ccD 3 1157:ℝ)) (by norm_num)
        (by simpa only [solver_K] using hK) (by simpa only [solver_K] using hn)
        (by simpa only [solver_K] using hlt) hD he0 he1
        (by simpa only [solver_K] using W_small l hl)
        (by intro lam B hlam hB; simpa only [solver_K, Nat.cast_ofNat] using solver_rate l lam B hlam hB)
      have hc : (ccD 3 1157:ℝ) ≠ 0 := by norm_num [ccD, GD]
      rw [mul_one_div_cancel hc] at hN
      norm_num only [Nat.cast_ofNat] at hN
      have hh := main_small l h32
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hm := mul_lt_mul_of_pos_right hh hn0
      have : (needD solver 3 (idx pieces 16 l) n (precision l):ℝ) < n := by
        have hdiv : (n:ℝ) / 2^precision l = (1/(2:ℝ)^precision l)*n := by ring
        rw [hdiv] at hN
        nlinarith only [hN, hm]
      exact this
    · have hs : precision l = 4 := by unfold precision; omega
      have h199 : 486 ≤ n := by
        have hx := linear_le_x l (by omega)
        have h199K : 486 ≤ K 16 l := by
          rw [K_eq]
          exact (show 486 ≤ 2^9 by norm_num).trans
            (Nat.pow_le_pow_right (by norm_num) (by omega : 9 ≤ x 16 l))
        omega
      have hU := SATNeed.ubD_precision_four_le (K 16 l) n (by omega)
      have hN := SATNeed.needD_le_of_ub (stArgD Net.Main.bounds)
        (stLowerD Net.Main.bounds) stBetaU solver (idx pieces 16 l)
        (C₀ := 1157) (k := 3) (n := n) (s := precision l) (a := 709)
        (A₁ := 1/(ccD 3 1157:ℝ)) (by simpa only [solver_K, hs] using hU)
        (by norm_num) (by simpa only [solver_K] using hK)
        (by simpa only [solver_K] using hn) (by simpa only [solver_K] using hlt)
        hD he0 he1 (by simpa only [solver_K] using W_small l hl)
        (by intro lam B hlam hB; simpa only [solver_K, Nat.cast_ofNat] using solver_rate l lam B hlam hB)
      have hc : (ccD 3 1157:ℝ) ≠ 0 := by norm_num [ccD, GD]
      rw [mul_one_div_cancel hc] at hN
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hN
      have hh := main_small_four l hl
      have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      rw [← hs] at hh
      have hm := mul_lt_mul_of_pos_right hh hn0
      have : (needD solver 3 (idx pieces 16 l) n (precision l):ℝ) < n := by
        have hdiv : (n:ℝ) / 2^precision l = (1/(2:ℝ)^precision l)*n := by ring
        rw [hdiv] at hN
        nlinarith only [hN, hm]
      exact this
  exact_mod_cast hN

theorem plan_lt (l n : ℕ) (hl : 18 ≤ l) (hn : K 16 l^17 ≤ n)
    (hn' : n < K 16 (l+1)^17) :
    (planAtD solver 3 n (idx pieces 16 l) (precision l)).getD n < n := by
  have hKn : K 16 l ≤ n := (Nat.le_self_pow (by norm_num) _).trans hn
  have h6 := (delta_six_le_K l hl).trans hKn
  have hb := (stBetaU 3 (precision l) (by norm_num)).2.1
  have hD : 2^betaU 3 (precision l) ≤ n+1 :=
    (Nat.le_self_pow (by norm_num) _).trans (h6.trans (by omega))
  have hs : s0U 3 ≤ precision l := by
    have hs3 : s0U 3 = 4 := by rfl
    rw [hs3, precision]
    omega
  exact (stPlanNeedD _ solver solver_poly 3 n (idx pieces 16 l) (precision l)
    hs hD (Arith.test3 hb h6)).trans_lt (need_lt l n hl hn hn')

/-- The actual level-selection program, with its original seventeenth-root rule. -/
def selected (n : ℕ) : ℕ := (pick (root17 n)).1.length

theorem picked_interval (n : ℕ) (hn : K 16 0^17 ≤ n) :
    K 16 (selected n)^17 ≤ n ∧ n < K 16 (selected n+1)^17 := by
  obtain ⟨hr1, hr2⟩ := root17_spec n
  obtain ⟨_, _, hp3, hp4⟩ := pick_spec pieces 16
  have h0 : K 16 0 ≤ (root17 n).length := by
    by_contra hh
    have h := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 hh)) 17
    exact (not_le_of_gt hr2) (h.trans hn)
  exact ⟨(Nat.pow_le_pow_left (hp3 _ h0) 17).trans hr1,
    hr2.trans_le (Nat.pow_le_pow_left (Nat.succ_le_of_lt (hp4 _)) 17)⟩

set_option exponentiation.threshold 10000 in
theorem binary_to_decimal (M : ℕ) : (2:ℕ)^(10000*M) ≤ 10^(3011*M) := by
  rw [pow_mul, pow_mul]
  exact Nat.pow_le_pow_left (show (2:ℕ)^10000 ≤ 10^3011 from by norm_num) M

theorem cutoff_of_exponent (l R M : ℕ) (h : x 16 l * 17 ≤ 10000*R)
    (h' : 3011*R ≤ M) : K 16 l^17 ≤ 10^M := by
  rw [K_eq, ← pow_mul]
  exact (Nat.pow_le_pow_right (by norm_num) h).trans
    ((binary_to_decimal R).trans (Nat.pow_le_pow_right (by norm_num) h'))

/-- The exact binary threshold is 2^240645710; this is a decimal upper bound. -/
theorem cutoff_ge : K 16 18^17 ≤ (10^72500000) := by
  apply cutoff_of_exponent 18 24065
  · have h := PartA.x_formula 16 18
    norm_num at h
    have hx : x 16 18 = 14155630 := by exact_mod_cast h
    rw [hx]
    norm_num
  · norm_num

theorem selected_ge_of (L n : ℕ) (hn : K 16 L^17 ≤ n) : L ≤ selected n := by
  have hL : K 16 L ≤ (root17 n).length := by
    by_contra hh
    have h := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 hh)) 17
    exact (not_le_of_gt (root17_spec n).2) (h.trans hn)
  have hm := (pick_spec pieces 16).2.2.2 (root17 n)
  have hh : K 16 L < K 16 (selected n+1) := hL.trans_lt hm
  exact Nat.le_of_lt_succ ((K_strictMono 16 le_rfl).lt_iff_lt.mp hh)

theorem selected_ge (n : ℕ) (hn : (10^72500000) ≤ n) : 18 ≤ selected n :=
  selected_ge_of 18 n (cutoff_ge.trans hn)

theorem first_level_le (L n : ℕ) (hn : K 16 L^17 ≤ n) : K 16 0^17 ≤ n :=
  (Nat.pow_le_pow_left ((K_strictMono 16 le_rfl).monotone (Nat.zero_le L)) 17).trans hn

/-- The proposed target of 10^100000 variables selects level eight. -/
theorem selected_at_target : selected (10^100000) = 8 := by
  have h8 : K 16 8^17 ≤ 10^100000 := by
    apply cutoff_of_exponent 8 24
    · have h := PartA.x_formula 16 8
      norm_num at h
      have hx : x 16 8 = 13738 := by exact_mod_cast h
      rw [hx]
      norm_num
    · norm_num
  have h9 : 10^100000 < K 16 9^17 := by
    have decimal_lt_binary (m r : ℕ) (hm : 4*m < r) : (10:ℕ)^m < 2^r := by
      have hp := Nat.pow_le_pow_left (show (10:ℕ) ≤ 2^4 from by decide) m
      rw [← pow_mul] at hp
      exact hp.trans_lt (Nat.pow_lt_pow_right (show 1 < (2:ℕ) from by decide) hm)
    have h := PartA.x_formula 16 9
    norm_num at h
    have hx : x 16 9 = 27556 := by exact_mod_cast h
    rw [K_eq, ← pow_mul, hx]
    exact decimal_lt_binary 100000 (27556*17) (by decide)
  have hlo := selected_ge_of 8 (10^100000) h8
  have hi := (picked_interval (10^100000) (first_level_le 8 _ h8)).1
  have hlt : K 16 (selected (10^100000)) < K 16 9 := by
    by_contra hh
    exact (not_le_of_gt h9) ((Nat.pow_le_pow_left (by omega : K 16 9 ≤ K 16 (selected (10^100000))) 17).trans hi)
  have hsel := (K_strictMono 16 le_rfl).lt_iff_lt.mp hlt
  omega

theorem chosen_plan_lt (n : ℕ) (hn : (10^72500000) ≤ n) :
    (planAtD solver 3 n (pick (root17 n)).2
      (precisionProgram (pick (root17 n)).1).length).getD n < n := by
  have h0 := first_level_le 18 n (cutoff_ge.trans hn)
  obtain ⟨h1, h2⟩ := picked_interval n h0
  change (planAtD solver 3 n (Pick.pick pieces 16 (root17 n)).2
    (precisionProgram (pick (root17 n)).1).length).getD n < n
  rw [(pick_spec pieces 16).2.1, precision_length]
  exact plan_lt (selected n) n (selected_ge n hn) h1 h2

/-- The complete counting algorithm, with the certified explicit piece constants. -/
def algorithm : List Bool × U → List Bool :=
  ABDG StepSparsify.thCal solver pick precisionProgram

def budget : List Bool → ℕ := eBD solver pick precisionProgram

theorem encoded_eD_lt {n : ℕ} (φ : Sat3.CNF n) (hφ : SatK.IsKCNF 3 φ)
    (hn : 10^72500000 ≤ n) : eD solver pick precisionProgram (SatM.enc 3 φ) < n := by
  obtain ⟨hk, hf⟩ := Decode.stDecM 3 n φ (by norm_num) hφ.1
  simpa only [eD, planD, kU, nU, idxU, precU, hk, hf, List.length_replicate] using
    chosen_plan_lt n hn

/-- This is a bound on the complete algorithm's budget, for every 3-CNF, without a density hypothesis. -/
theorem budget_lt {n : ℕ} (φ : Sat3.CNF n) (hφ : SatK.IsKCNF 3 φ)
    (hn : 10^72500000 ≤ n) : budget (SatM.enc 3 φ) < n :=
  (expBDc _ solver 3 pick precisionProgram n φ (by norm_num) hφ).1.trans_lt
    (encoded_eD_lt φ hφ hn)

/-- Above the explicit cutoff, neither branch selected by the merged program
uses its full-assignment exhaustive-counting fallback. Recursive base cases remain. -/
theorem no_fallback {n : ℕ} (φ : Sat3.CNF n) (hφ : SatK.IsKCNF 3 φ)
    (hn : 10^72500000 ≤ n) :
    (planD solver pick precisionProgram (SatM.enc 3 φ)).isNone = false ∧
    (useMD solver pick precisionProgram (SatM.enc 3 φ) = true →
      (planM solver pick (SatM.enc 3 φ)).isNone = false) := by
  have hd := encoded_eD_lt φ hφ hn
  have hb := budget_lt φ hφ hn
  have hf := (Decode.stDecM 3 n φ (by norm_num) hφ.1).2
  constructor
  · cases hp : planD solver pick precisionProgram (SatM.enc 3 φ) with
    | none => simp only [eD, hp, Option.getD_none, nU, hf, List.length_replicate] at hd; exact False.elim (Nat.lt_irrefl n hd)
    | some v => rfl
  · intro hu
    cases hp : planM solver pick (SatM.enc 3 φ) with
    | none =>
      simp only [budget, eBD, hu, cond_true, eM, hp, Option.getD_none, hf,
        List.length_replicate] at hb
      exact False.elim (Nat.lt_irrefl n hb)
    | some v => rfl

/-- The revised program still returns the exact number of satisfying assignments,
including below the cutoff, when supplied with its specified padding. -/
theorem algorithm_correct {n : ℕ} (φ : Sat3.CNF n) (hφ : SatK.IsKCNF 3 φ)
    (pad : U) (hpad : 2^budget (SatM.enc 3 φ) ≤ pad.length) :
    algorithm (SatM.enc 3 φ, pad) = SatK.binary n (SatK.numSat φ) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec pieces 16
  obtain ⟨C, Q, _, hpick⟩ := seq_of_pick Chain.stChain2 stRate2 solveG2 Need.stNeedG
    pieces rho 190 16 rho_ge rho_lt parameters.1 parameters.2.2 le_rfl (by norm_num)
    pick hp1 hp2 hp3 hp4
  have h := RecursionWithPieces.correctBDGAB StepSparsify.thCal StepSparsify.lcCal
    StepSparsify.servesCal _ solver (e rho 16) C Q solver_poly precisionProgram
    3 n φ (by norm_num) hφ pad
  rw [hpick] at h
  exact h hpad

theorem algorithm_poly : PolyT algorithm ∧ PolyT budget :=
  certBDGc StepSparsify.thCal StepSparsify.lcCal StepSparsify.servesCal _ solver
    solver_poly pick precisionProgram (pick_spec pieces 16).1 precision_poly

end ETHConstants.SAT
