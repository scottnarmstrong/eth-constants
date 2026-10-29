/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified in eth-constants (2026): give the network the occurrence bound of Calabro's thresholds for k ≤ 3.
-/
module

public import UniformInK.Top.ArithDefs
import ClauseBound.ParityChecks.Sizes
import ClauseBound.ParityChecks.ArithAux
import all ClauseBound.TopN.Arith
import ClauseBound.Alg.TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The arithmetic of the exponent: natural numbers, for an arbitrary β

Inequalities between natural numbers in the arithmetic of the exponent, for an arbitrary natural
number β: 2 ≤ 2^β for β ≥ 1, and lower bounds on `WofU β K`.
The last statement, `stBetaU`, says that, for k ≥ 1, β = `betaU k s` has k ≤ β and β + 3 ≤ 2^β, and
that β + 1 ≤ 35·k·(s+1).
Notation as in proof/sparsification/UniformInK/Top/ArithDefs.lean. -/

public section

namespace UniformInK.ArithNat

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks

variable {β k K n C₀ : ℕ}

/-- 2 ≤ 2^β if 1 ≤ β. -/
theorem two_le_D (hβ : 1 ≤ β) : 2 ≤ 2 ^ β := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) hβ

/-- Lower bounds on `WofU β K`: with b = β + 3, D = 2^β and Y = `K.size`, it is at least b·D, b²·Y,
b², b·Y, Y, b, D and 1. -/
theorem WofU_ge (hK : 1 ≤ K) : (β + 3) * 2 ^ β ≤ WofU β K ∧ (β + 3) ^ 2 * K.size ≤ WofU β K ∧
    (β + 3) ^ 2 ≤ WofU β K ∧ (β + 3) * K.size ≤ WofU β K ∧ K.size ≤ WofU β K ∧ β + 3 ≤ WofU β K ∧ 2 ^ β ≤ WofU β K ∧ 1 ≤ WofU β K := by
  unfold WofU
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK
  have hD : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  generalize K.size = Y at hY
  generalize 2 ^ β = D at hD
  have hb : 1 ≤ β + 3 := by omega
  generalize β + 3 = b at hb
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have m1 : b * D ≤ b ^ 2 * D * Y := by
    calc b * D ≤ b ^ 2 * D := Nat.mul_le_mul_right _ hbb
      _ ≤ b ^ 2 * D * Y := Nat.le_mul_of_pos_right _ hY
  have m2 : b ^ 2 * Y ≤ b ^ 2 * D * Y := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hD)
  have m3 : b ^ 2 ≤ b ^ 2 * Y := Nat.le_mul_of_pos_right _ hY
  have m4 : b * Y ≤ b ^ 2 * Y := Nat.mul_le_mul_right _ hbb
  have m5 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ h1
  have m6 : D ≤ b * D := Nat.le_mul_of_pos_left _ hb
  exact ⟨m1, m2, m3.trans m2, m4.trans m2, m5.trans m2, (hbb.trans m3).trans m2, m6.trans m1, (h1.trans m3).trans m2⟩

/-- k ≤ `betaU k s`. -/
theorem k_le_betaU (k s : ℕ) : k ≤ betaU k s := by
  unfold betaU
  nlinarith [Nat.zero_le (k * s)]

/-- β + 3 ≤ 2^β for β = `betaU k s` and k ≥ 1. -/
theorem b_le_DU {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaU k s + 3 ≤ 2 ^ betaU k s := by
  have h3 : 3 ≤ betaU k s := by
    unfold betaU
    nlinarith [Nat.zero_le (k * s)]
  obtain ⟨t, ht⟩ : ∃ t, betaU k s = t + 3 := ⟨betaU k s - 3, by omega⟩
  have h : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  rw [ht, pow_add]
  omega

/-- β + 1 ≤ 35·k·(s+1) for β = `betaU k s` and k ≥ 1. -/
theorem betaU_le_lin {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaU k s + 1 ≤ 35 * k * (s + 1) := by
  unfold betaU
  nlinarith [Nat.zero_le (k * s)]

/-- k + 3 ≤ `betaD k s` for k ≥ 1. -/
theorem le_betaD {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : k + 3 ≤ betaD k s := by
  unfold betaD
  split_ifs with h3
  · have h64 : 64 ≤ 32 * alpha3 s ^ 2 + 4 * alpha3 s + 6 := by
      have : 56 ≤ alpha3 s := by
        unfold alpha3
        have := Nat.one_le_two_pow (n := s)
        nlinarith
      nlinarith
    have hc : Nat.clog 2 64 ≤ Nat.clog 2 (32 * alpha3 s ^ 2 + 4 * alpha3 s + 6) := Nat.clog_mono_right 2 h64
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.clog_pow 2 6 (by norm_num)] at hc
    omega
  · unfold betaU
    nlinarith [Nat.zero_le (k * s)]

/-- `betaD k s` ≤ `betaU k s` for k ≥ 1. -/
theorem betaD_le_betaU {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaD k s ≤ betaU k s := by
  unfold betaD
  split_ifs with h3
  · refine Nat.clog_le_of_le_pow ?_
    have hs : s + 7 ≤ 2 ^ (s + 3) := by
      have := Nat.lt_two_pow_self (n := s)
      rw [pow_add]
      omega
    have ha : alpha3 s ≤ 2 ^ (2 * s + 6) := by
      unfold alpha3
      calc 8 * 2 ^ s * (s + 7) ≤ 8 * 2 ^ s * 2 ^ (s + 3) := Nat.mul_le_mul_left _ hs
        _ = 2 ^ (2 * s + 6) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]; congr 1; omega
    have ha1 : 1 ≤ alpha3 s := by
      unfold alpha3
      have := Nat.one_le_two_pow (n := s)
      nlinarith
    calc 32 * alpha3 s ^ 2 + 4 * alpha3 s + 6 ≤ 64 * alpha3 s ^ 2 := by nlinarith
      _ ≤ 64 * (2 ^ (2 * s + 6)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 2)
      _ = 2 ^ (4 * s + 18) := by rw [← pow_mul, show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ betaU k s := Nat.pow_le_pow_right (by norm_num) (by unfold betaU; nlinarith [Nat.zero_le (k * s)])
  · exact le_rfl

/-- `blockD k n s` = 2^(`betaD k s`) if 2^(`betaU k s`) ≤ n + 1 and k ≥ 1. -/
theorem blockD_eq {k n s : ℕ} (hk : 1 ≤ k) (hD : 2 ^ betaU k s ≤ n + 1) : blockD k n s = 2 ^ betaD k s :=
  min_eq_left ((Nat.pow_le_pow_right (by norm_num) (betaD_le_betaU s hk)).trans hD)

end UniformInK.ArithNat

namespace UniformInK

/-- What is used of β = `betaU k s`. -/
theorem stBetaU : StBetaU := fun k s hk => ⟨ArithNat.k_le_betaU k s, ArithNat.b_le_DU s hk, ArithNat.betaU_le_lin s hk⟩

end UniformInK
