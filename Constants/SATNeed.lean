/-
Adapted from Anthropic's VariableBound/Top/ArithNeed.lean, Apache 2.0.
Keep the exact sparsification parameter and permit a real error coefficient.
-/
module
public import VariableBound.Top.ArithNeed
import all ClauseBound.ParityChecks.ArithOL
import all ClauseBound.TopN.Arith
import ClauseBound.Alg.TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section
namespace ETHConstants.SATNeed
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg
open ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
open ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL UniformInK
open VariableBound VariableBound.Net VariableBound.ArithNeed
/-- Preserve a separately proved leading coefficient for the network cost. -/
theorem needD_le_of_ub (hA : StArgD) (hL : StLowerD) (hB : StBetaU) {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n s a : ℕ} {A₁ : ℝ}
    (hUb : UbD k (S.K i) n (2 ^ betaU k s) ≤ a * n + 18 * S.K i ^ 16)
    (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (hD : 2 ^ betaU k s ≤ n + 1) (he0 : 0 < e) (he1 : e ≤ 1)
    (hM : ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needD S k i n s : ℝ) ≤ ((a : ℝ) + (ccD k C₀ : ℝ) * A₁) * n * e + n / (2:ℝ)^s := by
  obtain ⟨hkβ, hbD, hlin⟩ := hB k s hk
  have hβ1 : 1 ≤ betaU k s := hk.trans hkβ
  have hK1 : 1 ≤ S.K i := by omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := lowerDR hL (k := k) (s := s) (C₀ := C₀) hβ1 hkβ hK hn17 hlt
  have harg := hA (betaU k s) k (S.K i) n C₀ hkβ hbD hK hn17 hlt hD
  have hlam1 := one_le_lamS hK1 (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))
  have hlamK := lamS_mul_le (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))
  have hB1 : 1 ≤ bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) := by
    have b1 : 1 ≤ BbD k n := by unfold BbD BD; omega
    have b2 : 1 ≤ 2 * (3 * S.K i ^ 8) / S.K i := by
      rw [Arith.two_g_div hK1]
      exact Nat.mul_pos (by norm_num) (by positivity)
    unfold bitsS
    exact (Nat.mul_pos (Nat.mul_pos b1 (Nat.add_pos_left b2 _)) hK1).trans_le (Nat.le_add_left _ _)
  have hr := hrate _ _ hlam1 hB1
  have hsum := needD_le_sum S i hD
  have hlog : Real.logb 2 ((S.K i : ℝ) * ((lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) : ℝ) +
      (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) : ℝ))) ≤ ((5 * (17 * C₀ * (S.K i).size) + 16 : ℕ) : ℝ) := by
    have h := logb_le_of_le_pow _ _ (Nat.mul_pos hK1 (Nat.add_pos_left hlam1 _)) harg
    push_cast at h ⊢
    exact h
  generalize S.need (i, List.replicate (lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s))) (),
    List.replicate (bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n)) ()) = nd at hr hsum
  generalize bitsS (S.K i) (3 * S.K i ^ 8) (PbD (S.K i) n (2 ^ betaU k s)) (BbD k n) = Bt at hr hlog
  generalize lamS (S.K i) (3 * S.K i ^ 8) (UbD k (S.K i) n (2 ^ betaU k s)) (PbD (S.K i) n (2 ^ betaU k s)) = lam at hr hlog hsum r3 hlamK
  have rU : ((UbD k (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) ≤ (a : ℝ) * n + ((18 * S.K i ^ 16 : ℕ) : ℝ) := by exact_mod_cast hUb
  have rL : (lam : ℝ) * (S.K i : ℝ) ^ 3 ≤ (S.K i : ℝ) ^ 3 + (S.K i : ℝ) * ((UbD k (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) +
      ((3 * S.K i ^ 8 * PbD (S.K i) n (2 ^ betaU k s) : ℕ) : ℝ) := by
    exact_mod_cast hlamK
  have rS : (needD S k i n s : ℝ) ≤ (((3 * S.K i ^ 8 * (S.K i).size : ℕ) : ℝ) + ((PbD (S.K i) n (2 ^ betaU k s) * (2 * (3 * S.K i ^ 8) / S.K i + 1) : ℕ) : ℝ) +
      (((S.K i - 1) * lam : ℕ) : ℝ) + (nd : ℝ) + ((3 * S.K i ^ 8 * (3 * S.K i ^ 8) * 2 * Nat.size (objMax n (2 ^ betaU k s)) : ℕ) : ℝ) +
      ((Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ betaU k s) + 1) * (Nat.size (2 ^ betaU k s * n) + 2) + 8) + 2 + (betaU k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ)) +
      ((n / 2 ^ s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have rdiv : ((n / 2 ^ s : ℕ) : ℝ) ≤ (n : ℝ) / (2:ℝ)^s := by
    exact_mod_cast (Nat.cast_div_le (m := n) (n := 2^s) : ((n / 2^s:ℕ):ℝ) ≤ (n:ℝ)/(2^s:ℕ))
  have hKr : (0 : ℝ) < (S.K i : ℝ) := by exact_mod_cast hK1
  have core := real_coreM (A := (A₁ : ℝ)) hKr he0 he1 (Nat.cast_nonneg n) (Nat.cast_nonneg C₀) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hM r1 r2 r3 r4 r5 r6 r7 r8 r9 rU rL hr hlog
  have ecc : (3 + ((3 * GD C₀ : ℕ) : ℝ) + ((19 + 140 * k + GD C₀ : ℕ) : ℝ) + (GD C₀ : ℝ) + 18 + 1 + ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) + ((18 * (4 + 17 * C₀) : ℕ) : ℝ) +
      ((10 + 34 * C₀ : ℕ) : ℝ)) * (A₁ : ℝ) = ((ccD k C₀ : ℝ) * A₁) := by
    unfold ccD; push_cast; ring
  rw [ecc] at core
  calc
    (needD S k i n s : ℝ) ≤ e * ((a : ℝ) * n) +
        ((ccD k C₀ : ℝ) * A₁) * (n * e) + n / (2:ℝ)^s := by linarith
    _ = ((a : ℝ) + (ccD k C₀ : ℝ) * A₁) * n * e + n / (2:ℝ)^s := by ring

theorem needD_le_exact (hU : StUbD) (hA : StArgD) (hL : StLowerD) (hB : StBetaU) {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) {e : ℝ} {C₀ k n s : ℕ} {A₁ : ℝ}
    (hk : 1 ≤ k) (hK : 2 ≤ S.K i) (hn17 : S.K i ^ 17 ≤ n)
    (hlt : n < S.K i ^ (17 * C₀)) (hD : 2 ^ betaU k s ≤ n + 1) (he0 : 0 < e) (he1 : e ≤ 1)
    (hM : ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needD S k i n s : ℝ) ≤ (140 * k * ((betaU k s + 1 : ℕ) : ℝ) + (ccD k C₀ : ℝ) * A₁) * n * e + n / (2:ℝ)^s := by
  have hK1 : 1 ≤ S.K i := by omega
  have hKn : S.K i ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hU' := hU (betaU k s) k (S.K i) n (hk.trans (hB k s hk).1) (hK1.trans hKn)
  have h := needD_le_of_ub hA hL hB S i
    (a := 140 * k * (betaU k s + 1)) (by nlinarith only [hU'])
    hk hK hn17 hlt hD he0 he1 hM hrate
  push_cast at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Evaluate the logarithm at precision four instead of using the uniform coefficient 140. -/
theorem ubD_precision_four_le (K n : ℕ) (hn : 199 ≤ n) :
    UbD 3 K n (2 ^ betaU 3 4) ≤ 17928 * n + 18 * K ^ 16 := by
  have hc : Nat.clog 2 (96 * 2 ^ 198 * 199) = 213 := by decide
  change UbD 3 K n (2 ^ 198) ≤ 17928 * n + 18 * K ^ 16
  unfold UbD
  rw [LD_two_pow]
  rw [show 198 + 1 = 199 from rfl, hc]
  nlinarith only [hn]

end ETHConstants.SATNeed
