/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Upper-bound arguments adapted from GeneralPieces.Ring.Bits.
-/
module

public import SharperPartitions
public import PartitionEncoding
public import GeneralPieces.Half.Main
public import GeneralPieces.Main

/-! Explicit constants for the existing partition-based tensor-piece programs. -/

public section

namespace ETHConstants.ExplicitPieces

open Finset Real Partitions AppHalfPieces GeneralPieces.Bits GeneralPieces.Sizes
open ClauseBound.Inst.Half

/-- The upper partition estimate needs no additive constant. -/
theorem log_partition_upper (E : ℕ) : logb 2 (p E) ≤ kappa * √(E : ℝ) := by
  have h := Real.logb_le_logb_of_le one_lt_two
    (show (0 : ℝ) < p E by exact_mod_cast ClauseBound.Part.p_pos E)
    (ClauseBound.Part.p_le_exp E)
  rwa [ClauseBound.Part.Bounds.logb_exp, ← ClauseBound.Part.Bounds.kappa_mul] at h

/-- Explicit logarithmic bounds; the upper half is stronger than stated. -/
theorem partition_bounds : Partitions.Bounds 16 5 := by
  refine ⟨fun E hE => ?_, fun E => by linarith [log_partition_upper E]⟩
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have h := Real.logb_le_logb_of_le one_lt_two
    (show 0 < exp (-3) * exp (cHR * √(E : ℝ)) / (E : ℝ) ^ 16 by positivity)
    (Partition.explicit_partition_lower_bound E hE)
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    ClauseBound.Part.Bounds.logb_exp, ClauseBound.Part.Bounds.logb_exp,
    Real.logb_pow, ← ClauseBound.Part.Bounds.kappa_mul] at h
  have hc : (-5 : ℝ) ≤ (-3 : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  norm_num at h
  linarith

theorem kappa_le_four : kappa ≤ 4 := by
  unfold kappa
  rw [div_le_iff₀ (Real.log_pos (by norm_num))]
  linarith [Partition.cHR_bounds.2, Real.log_two_gt_d9]

theorem hOf_le (lam : ℕ) (hl : 1 ≤ lam) : AppHalfPieces.hOf lam ≤ 2 * lam ^ 2 := by
  rw [GeneralPieces.Lex.hOf_eq]
  exact PartitionEncoding.hOf_le lam hl

/-- Keep the negative constant in log h ≤ 2 log(2λ) − 1. -/
theorem log_hOf_le (lam : ℕ) (hl : 1 ≤ lam) :
    logb 2 (AppHalfPieces.hOf lam) ≤ 2 * logb 2 (2 * lam) - 1 := by
  have hl0 : (0 : ℝ) < lam := by exact_mod_cast hl
  have hh0 : (0 : ℝ) < AppHalfPieces.hOf lam := by
    exact_mod_cast (show 0 < AppHalfPieces.hOf lam from lt_of_lt_of_le (by norm_num) (GeneralPieces.hOfSpec lam).1)
  have h := Real.logb_le_logb_of_le one_lt_two hh0
    (show (AppHalfPieces.hOf lam : ℝ) ≤ 2 * (lam : ℝ) ^ 2 by exact_mod_cast hOf_le lam hl)
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at h
  rw [Real.logb_mul (by norm_num) hl0.ne', Real.logb_self_eq_one (by norm_num)]
  norm_num at h
  linarith

/-- An explicit version of the estimate driving the rank reduction. -/
theorem kappa_sqrt_hOf_le (lam : ℕ) (hl : 1 ≤ lam) :
    kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ lam + 32 * logb 2 (2 * lam) - 7 := by
  have h1 := kappa_sqrt_pred_lt partition_bounds (by norm_num) hl
  have h2 := kappa_sqrt_le_pred (h := AppHalfPieces.hOf lam)
    (le_trans (by norm_num) (GeneralPieces.hOfSpec lam).1)
  have h3 := log_hOf_le lam hl
  linarith [kappa_le_four]

/-- By display (46): if 1 ≤ r ≤ k·p(a), then log r ≤ log k + κ√a. -/
theorem logb_le_of_le_mul_p {r k a : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (h : r ≤ k * p a) :
    logb 2 r ≤ logb 2 k + kappa * √(a : ℝ) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < p a := by exact_mod_cast ClauseBound.Part.p_pos a
  have h1 : (r : ℝ) ≤ k * p a := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hr0 h1
  rw [Real.logb_mul hk0.ne' hp0.ne'] at h2
  linarith [log_partition_upper a]

/-- The display, first inequality: c^row_s + c^col_s ≤ 2√2·κ√h + 2·log(2h+1) + 2C + 2, for |s| ≤ 2h. -/
theorem bits_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) :
    ((Nat.clog 2 (Rrow h s) + Nat.clog 2 (Rcol h s) : ℕ) : ℝ) ≤ 2 * √2 * (kappa * √(h : ℝ)) + 2 * logb 2 (2 * (h : ℝ) + 1) + 2 := by
  obtain ⟨a1, a2⟩ := abs_le.1 hs
  have r1 : 1 ≤ Rrow h s := ClauseBound.Part.one_le_Rrow hs
  have r2 : 1 ≤ Rcol h s := ClauseBound.Part.one_le_Rcol hs
  have q1 : pZ (2 * h + s) = p (2 * (h : ℤ) + s).toNat := if_pos (by omega)
  have q2 : pZ (2 * h - s) = p (2 * (h : ℤ) - s).toNat := if_pos (by omega)
  have c1 : (((2 * (h : ℤ) + s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) + s := by
    have : (((2 * (h : ℤ) + s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) + s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have c2 : (((2 * (h : ℤ) - s).toNat : ℕ) : ℝ) = 2 * (h : ℝ) - s := by
    have : (((2 * (h : ℤ) - s).toNat : ℕ) : ℤ) = 2 * (h : ℤ) - s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have h3 := ClauseBound.Part.Bits.clog_le r1 (logb_le_of_le_mul_p r1 (Nat.succ_pos _) (q1 ▸ Rrow_le h s))
  have h4 := ClauseBound.Part.Bits.clog_le r2 (logb_le_of_le_mul_p r2 (Nat.succ_pos _) (q2 ▸ Rcol_le h s))
  rw [c1] at h3
  rw [c2] at h4
  have h5 := mul_le_mul_of_nonneg_left (sqrt_add_sqrt_le hs) ClauseBound.Part.Bits.kappa_pos.le
  have h6 : √(2 * (h : ℝ)) = √2 * √(h : ℝ) := Real.sqrt_mul (by norm_num) _
  rw [h6] at h5
  push_cast at h3 h4 ⊢
  linarith


/-- Explicit cap sum for every piece and every positive bit length. -/
theorem caps_le (lam : ℕ) (hl : 1 ≤ lam) (s : ℤ)
    (hs : |s| ≤ 2 * (AppHalfPieces.hOf lam : ℤ)) :
    ((Nat.clog 2 (Rrow (AppHalfPieces.hOf lam) s) +
      Nat.clog 2 (Rcol (AppHalfPieces.hOf lam) s) : ℕ) : ℝ) ≤
      4 * (1 / √2) * lam + 95 * logb 2 (2 * lam) := by
  have h1 := bits_le hs
  have h2 := kappa_sqrt_hOf_le lam hl
  have h3 := ClauseBound.Part.Bits.logb_succ_le (k := 2) (h := AppHalfPieces.hOf lam)
    (by norm_num) (le_trans (by norm_num) (GeneralPieces.hOfSpec lam).1)
  have h4 := log_hOf_le lam hl
  have hL : 0 ≤ logb 2 (2 * lam) := Real.logb_nonneg one_lt_two (by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith)
  have hsqrt : √(2 : ℝ) ≤ 99 / 70 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * √(2 : ℝ) by positivity)
  have hcoef := mul_le_mul_of_nonneg_right hsqrt hL
  push_cast at h3
  rw [four_mul_rho]
  have hs1 : (1 : ℝ) ≤ √2 := by norm_num
  nlinarith [hs1]

/-- A direct uniform bound on the total partition table. -/
theorem delta_le (lam : ℕ) (hl : 1 ≤ lam) :
    Delta (AppHalfPieces.hOf lam) ≤ 2 ^ (16 * lam) := by
  have hh := hOf_le lam hl
  have hl0 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hroot : √(AppHalfPieces.hOf lam : ℝ) ≤ (3 / 2) * lam := by
    apply (Real.sqrt_le_left (by positivity)).2
    have : (AppHalfPieces.hOf lam : ℝ) ≤ 2 * (lam : ℝ) ^ 2 := by exact_mod_cast hh
    nlinarith [sq_nonneg (lam : ℝ)]
  have hk : kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ 6 * lam :=
    calc kappa * √(AppHalfPieces.hOf lam : ℝ) ≤ 4 * ((3 / 2 : ℝ) * lam) :=
      mul_le_mul kappa_le_four hroot (Real.sqrt_nonneg _) (by norm_num)
      _ = _ := by ring
  have hdpos : 1 ≤ Delta (AppHalfPieces.hOf lam) :=
    (ClauseBound.Part.p_pos 0).trans (single_le_sum (f := p)
      (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.succ_pos _)))
  have hD := logb_le_of_le_mul_p hdpos (Nat.succ_pos _) (Delta_le (AppHalfPieces.hOf lam))
  have hsqrt : √((4 * AppHalfPieces.hOf lam : ℕ) : ℝ) =
      2 * √(AppHalfPieces.hOf lam : ℝ) := by
    push_cast
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hsqrt] at hD
  have hlog := ClauseBound.Part.Bits.logb_succ_le (k := 4) (h := AppHalfPieces.hOf lam)
    le_rfl (le_trans (by norm_num) (GeneralPieces.hOfSpec lam).1)
  have hlogh := log_hOf_le lam hl
  have hlogl := logb_two_mul_le hl
  apply ClauseBound.Part.Bits.le_two_pow_of_logb_le hdpos hD
  push_cast at hlog ⊢
  nlinarith

/-- The magnitude bound needs degree nine, rather than the crude degree 380. -/
theorem big_le (lam : ℕ) (hl : 1 ≤ lam) :
    ClauseBound.Boson.big (AppHalfPieces.hOf lam) ≤ (2 * lam) ^ 9 := by
  have hh := hOf_le lam hl
  have hD := delta_le lam hl
  have hc : Nat.clog 2 (Delta (AppHalfPieces.hOf lam)) ≤ 16 * lam :=
    Nat.clog_le_of_le_pow hD
  have h1 : AppHalfPieces.hOf lam + 1 ≤ 3 * lam ^ 2 := by
    have : 1 ≤ lam ^ 2 := Nat.one_le_pow _ _ hl
    omega
  have h2 := Nat.pow_le_pow_left h1 2
  have h3 : lam ≤ lam ^ 4 := Nat.le_self_pow (by norm_num) lam
  have h4 : lam ^ 4 ≤ lam ^ 9 := Nat.pow_le_pow_right hl (by norm_num)
  change 40 * (AppHalfPieces.hOf lam + 1) ^ 2 + Nat.clog 2 (Delta _) ≤ _
  rw [mul_pow]
  norm_num
  nlinarith

/-- All numerical obligations of the actual programs, with explicit constants. -/
theorem cst (lam : ℕ) (hl : 1 ≤ lam) : Cst 2 95 lam := by
  have hh := hOf_le lam hl
  have hD := delta_le lam hl
  have hbig := big_le lam hl
  have hpad := GeneralPieces.Consts.pad_le hl hh hD
  have hpow : (2 * lam) ^ 9 ≤ (2 * lam) ^ 95 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have hcnt := (ClauseBound.Boson.Final.four_mul_add_one_le_big (AppHalfPieces.hOf lam)).trans (hbig.trans hpow)
  have hfact := (ClauseBound.Boson.Final.factorial_lt_two_pow_big (AppHalfPieces.hOf lam)).trans_le
    (Nat.pow_le_pow_right (by norm_num) (hbig.trans hpow))
  rw [GeneralPieces.Lex.hOf_eq] at hh hD hbig hpad hcnt hfact
  refine ⟨hh, hcnt, hfact, hbig.trans hpow,
    hpad.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by norm_num))),
    fun s hs => ?_⟩
  have hcaps := caps_le lam hl s (by rwa [GeneralPieces.Lex.hOf_eq])
  rw [GeneralPieces.Lex.hOf_eq] at hcaps
  have hsum := GeneralPieces.Consts.cap_le (c := 95) hl hcaps
  have hlarge : (3 + 95) * lam ≤ 2 * 95 * lam := by omega
  exact ⟨(Nat.le_add_right _ _).trans (hsum.trans hlarge),
    (Nat.le_add_left _ _).trans (hsum.trans hlarge), hcaps⟩

/-- These are the original piece programs, with the new checked parameters. -/
theorem par : ClauseBound.Gen.Par (halfF 2 95) (1 / √2) 95 :=
  ClauseBound.Inst.Half.Par.par_of_cst
    (GeneralPieces.stSpec AppHalfPieces.pieceFacts) cst

/-- The functions computed by those programs are the original tensor pieces. -/
theorem realizes (lam : ℕ) (hl : 1 ≤ lam) :
    GeneralPieces.Realizes (halfF 2 95) 0 lam (GeneralPieces.halfA lam) :=
  GeneralPieces.half_realizes AppHalfPieces.pieceFacts 0 hl (cst lam hl)

/-- All clauses of the padded-operation piece interface, with a numerical constant. -/
theorem isPieces : AppRunningTime.IsPieces (1 / √2) 190 (halfF 2 95)
    GeneralPieces.halfA (GeneralPieces.valOf (halfF 2 95)) := by
  exact GeneralPieces.of_par_realizes par (Cert.halfF_keeps 2 95)
    ClauseBound.Inst.Half.half_le ClauseBound.Inst.Half.lt_one realizes

end ETHConstants.ExplicitPieces
