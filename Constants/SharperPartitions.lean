/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

The induction below is adapted from ClauseBound.Part.Lower. The sharper
third-moment estimate and the resulting constants are local additions.
-/
module

public import ClauseBound.Part.Lower
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! A stronger partition lower bound, using the same induction as the upstream
formalization. The key is to retain the exact third geometric moment. -/

public section

namespace ETHConstants.Partition

open Finset Partitions ClauseBound.Part ClauseBound.Part.Lower

theorem cube_choose (v : ℕ) :
    (v : ℝ) ^ 3 = 6 * ((v + 1).choose 3 : ℝ) + v := by
  rcases v with _ | v
  · norm_num [Nat.choose]
  rcases v with _ | v
  · norm_num [Nat.choose]
  have h := Nat.descFactorial_eq_factorial_mul_choose (v + 3) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  norm_num at h
  rw [show v + 3 - 2 = v + 1 by omega] at h
  have h' : ((v : ℝ) + 1) * (((v : ℝ) + 2) * ((v : ℝ) + 3)) =
      6 * ((v + 3).choose 3 : ℝ) := by exact_mod_cast h
  push_cast
  nlinarith only [h']

theorem third_moment_eq {r : ℝ} (hr : ‖r‖ < 1) :
    ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v =
      r / (1 - r) ^ 2 + 6 * (r / (1 - r) ^ 2) ^ 2 := by
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hr).mul_left (r ^ 2)
  have ht : HasSum (fun n : ℕ => ((n + 2 + 1).choose 3 : ℝ) * r ^ (n + 2))
      (r ^ 2 / (1 - r) ^ 4) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, pow_add, mul_assoc, mul_comm,
      mul_left_comm, div_eq_mul_inv, one_mul] using hs
  have hz : HasSum (fun n : ℕ => ((n + 1).choose 3 : ℝ) * r ^ n)
      (r ^ 2 / (1 - r) ^ 4) := by
    have h := (hasSum_nat_add_iff
      (f := fun n : ℕ => ((n + 1).choose 3 : ℝ) * r ^ n)
      (g := r ^ 2 / (1 - r) ^ 4) 2).mp ht
    have hzero : (∑ i ∈ range 2, ((i + 1).choose 3 : ℝ) * r ^ i) = 0 := by
      norm_num [sum_range_succ, Nat.choose]
    rw [hzero, add_zero] at h
    exact h
  have hsum := (hz.mul_left 6).add (hasSum_coe_mul_geometric_of_norm_lt_one hr)
  have hfun : (fun n : ℕ => 6 * (((n + 1).choose 3 : ℝ) * r ^ n) + (n : ℝ) * r ^ n) =
      (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n) := by
    ext n
    rw [cube_choose]
    ring
  rw [hfun] at hsum
  rw [hsum.tsum_eq]
  simp only [div_pow, ← pow_mul, Nat.reduceMul]
  ring

theorem first_moment_exp_le {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤ 1 / y ^ 2 := by
  have hE : 0 < Real.exp (y / 2) := Real.exp_pos _
  have hE1 : 1 < Real.exp (y / 2) := Real.one_lt_exp_iff.2 (by positivity)
  have e1 : Real.exp (-y) = 1 / Real.exp (y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have e2 : Real.sinh (y / 2) = (Real.exp (y / 2) - 1 / Real.exp (y / 2)) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, one_div]
  have hs : y / 2 ≤ Real.sinh (y / 2) := Real.self_le_sinh_iff.mpr (by positivity)
  have hpos : 0 < Real.sinh (y / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hbound : 1 / 4 * (1 / Real.sinh (y / 2) ^ 2) ≤ 1 / y ^ 2 := by
    calc
      _ ≤ 1 / 4 * (1 / (y / 2) ^ 2) := by gcongr
      _ = _ := by field_simp; ring
  rw [e2] at hbound
  rw [e1]
  generalize Real.exp (y / 2) = E at *
  have hE2 : E ^ 2 - 1 ≠ 0 := by nlinarith only [hE1]
  have e3 : 1 / E ^ 2 / (1 - 1 / E ^ 2) ^ 2 =
      1 / 4 * (1 / ((E - 1 / E) / 2) ^ 2) := by
    have a : E - 1 / E = (E ^ 2 - 1) / E := by field_simp
    have b : 1 - 1 / E ^ 2 = (E ^ 2 - 1) / E ^ 2 := by field_simp
    rw [a, b]
    field_simp
    ring
  rw [e3]
  exact hbound

/-- The upstream bound is 486/y^4. Retaining the exact moment gives (70/9)/y^4. -/
theorem third_moment_exp_le {y : ℝ} (hy : 0 < y) (hy2 : y ≤ 4 / 3) :
    ∑' v : ℕ, (v : ℝ) ^ 3 * (Real.exp (-y)) ^ v ≤ (70 / 9) / y ^ 4 := by
  have hr : ‖Real.exp (-y)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    linarith only [hy]
  rw [third_moment_eq hr]
  have h := first_moment_exp_le hy
  have h0 : 0 ≤ Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 := by positivity
  calc
    _ ≤ 1 / y ^ 2 + 6 * (1 / y ^ 2) ^ 2 := by gcongr
    _ ≤ (70 / 9) / y ^ 4 := by
      field_simp
      nlinarith only [hy, hy2]

/-- Σ_{1 ≤ v ≤ n} v·e^{−yv}·(1 − η·v²) ≥ 1/y² − 1/4 − (70/9)·η/y⁴ if 0 < y ≤ 4/3 and the terms with v > n
are not positive. -/
theorem sum_v_ge {y η : ℝ} (hy : 0 < y) (hy2 : y ≤ 4 / 3) (hη : 0 ≤ η) (n : ℕ) (hn : 1 ≤ η * (n : ℝ) ^ 2) :
    1 / y ^ 2 - 1 / 4 - (70 / 9) * η / y ^ 4 ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(y * v)) * (1 - η * (v : ℝ) ^ 2) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.exp (-y) := ⟨_, rfl⟩
  have r0 : 0 < r := hr ▸ Real.exp_pos _
  have r1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg r0.le]
  have e (v : ℕ) : Real.exp (-(y * v)) = r ^ v := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  have hG : HasSum (fun v : ℕ => (v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) (r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).sub ((summable_pow_mul_geometric_of_norm_lt_one 3 hnorm).hasSum.mul_left η)
  have hle : r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ ∑ v ∈ Icc 1 n, ((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) := by
    have h := sum_le_hasSum (Icc 1 n) (fun v hv => ?_) hG.neg
    · rw [Finset.sum_neg_distrib] at h
      linarith
    · have e2 : -((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) = (v : ℝ) * r ^ v * (η * (v : ℝ) ^ 2 - 1) := by ring
      rw [e2]
      rcases Nat.eq_zero_or_pos v with rfl | hv0
      · simp
      · have hvn : n < v := by
          by_contra hcon
          exact hv (Finset.mem_Icc.2 ⟨hv0, not_lt.1 hcon⟩)
        have hvn' : (n : ℝ) ≤ v := by exact_mod_cast hvn.le
        have h2 : η * (n : ℝ) ^ 2 ≤ η * (v : ℝ) ^ 2 := by gcongr
        exact mul_nonneg (by positivity) (by linarith)
  have h3 : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ (70 / 9) / y ^ 4 := by
    rw [hr]
    exact third_moment_exp_le hy hy2
  have h5 : 1 / y ^ 2 - 1 / 4 ≤ r / (1 - r) ^ 2 := hr ▸ T1_ge hy
  have h6 : η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ (70 / 9) * η / y ^ 4 := by
    calc _ ≤ η * ((70 / 9) / y ^ 4) := by gcongr
      _ = _ := by ring
  calc _ ≤ r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v := by linarith
    _ ≤ _ := hle
    _ = _ := Finset.sum_congr rfl fun v _ => by rw [e]; ring

/-! ### The sum over k -/

/-- The sum over 1 ≤ k ≤ K of the lower bounds for the sums over v. -/
theorem sum_k_ge {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {K : ℕ} (hK : 1 ≤ K) :
    1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) - K / 4 - (70 / 9) * γ / α ^ 4 * (Real.pi ^ 2 / 6)
      ≤ ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - (70 / 9) * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
  have e : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - (70 / 9) * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      = 1 / α ^ 2 * (1 / (k : ℝ) ^ 2) - 1 / 4 - (70 / 9) * γ / α ^ 4 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.1 hk).1
    field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Ioc, nsmul_eq_mul]
  have h1 := le_sum_inv_sq hK
  have h2 := sum_inv_sq_le K
  have h3 : 1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) ≤ 1 / α ^ 2 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by gcongr
  have h4 : (70 / 9) * γ / α ^ 4 * ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 ≤ (70 / 9) * γ / α ^ 4 * (Real.pi ^ 2 / 6) := by gcongr
  have h5 : ((K - 0 : ℕ) : ℝ) * (1 / 4) = K / 4 := by simp; ring
  linarith

theorem cHR_bounds : (5 / 2 : ℝ) ≤ cHR ∧ cHR ≤ 13 / 5 := by
  have hs : 0 ≤ Real.sqrt (2 / 3 : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hl : (4 / 5 : ℝ) ≤ Real.sqrt (2 / 3 : ℝ) := by nlinarith only [hs, hs2]
  have hu : Real.sqrt (2 / 3 : ℝ) ≤ 33 / 40 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  constructor
  · calc
      (5 / 2 : ℝ) ≤ (157 / 50) * (4 / 5) := by norm_num
      _ ≤ Real.pi * Real.sqrt (2 / 3 : ℝ) :=
        mul_le_mul (by linarith [Real.pi_gt_d2]) hl (by norm_num) Real.pi_pos.le
      _ = cHR := rfl
  · calc
      cHR ≤ (63 / 20 : ℝ) * (33 / 40) :=
        mul_le_mul (by linarith [Real.pi_lt_d2]) hu hs (by norm_num)
      _ ≤ 13 / 5 := by norm_num

/-! ### The arithmetic of the induction step -/

/-- With s = √n, α = c/(2s) − B/s², γ = c/(2s³), c² = 4Z and 1/α ≤ K ≤ 1/α + 1, the lower bound for
the double sum is at least n, if B ≥ 16 and s ≥ 7B/c + c. -/
theorem step_arith {c s B α γ Z : ℝ} {K : ℕ} (hc : 0 < c) (hB : 16 ≤ B) (hs : 7 * B / c + c ≤ s) (hα : α = c / (2 * s) - B / s ^ 2)
    (hγ : γ = c / (2 * s ^ 3)) (hZ : Z = c ^ 2 / 4) (hK1 : 1 / α ≤ K) (hK2 : (K : ℝ) ≤ 1 / α + 1) :
    s ^ 2 ≤ 1 / α ^ 2 * (Z - 1 / K) - K / 4 - (70 / 9) * γ / α ^ 4 * Z := by
  have hBc : 0 < 7 * B / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 7 * B ≤ c * s := by
    have : 7 * B / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  obtain ⟨q, hq⟩ : ∃ q, q = c * s - 2 * B := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = 2 * s ^ 2 / q := ⟨_, rfl⟩
  have hαw : α = 1 / w := by
    rw [hα, hw, hq]
    have : c * s - 2 * B ≠ 0 := by linarith
    field_simp
  have hw0 : 0 < w := by rw [hw]; positivity
  have e1 : 1 / α = w := by rw [hαw]; field_simp
  have e2 : 1 / α ^ 2 = w ^ 2 := by rw [hαw]; field_simp
  have e4 : (70 / 9) * γ / α ^ 4 = (70 / 9) * γ * w ^ 4 := by rw [hαw]; field_simp
  rw [e1] at hK1 hK2
  rw [e2, e4]
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hw0 hK1
  -- the gain
  have g1 : s ^ 2 + 4 * B * s / c ≤ w ^ 2 * Z := by
    rw [hw, hZ]
    have e5 : (2 * s ^ 2 / q) ^ 2 * (c ^ 2 / 4) = c ^ 2 * s ^ 4 / q ^ 2 := by field_simp; ring
    rw [e5, le_div_iff₀ (by positivity)]
    have e6 : (s ^ 2 + 4 * B * s / c) * q ^ 2 = s * ((c * s + 4 * B) * q ^ 2) / c := by field_simp
    rw [e6, div_le_iff₀ hc, hq]
    have h7 : (c * s + 4 * B) * (c * s - 2 * B) ^ 2 ≤ (c * s) ^ 3 := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ B) (by linarith : (0:ℝ) ≤ B)) (by linarith : (0:ℝ) ≤ 12 * (c * s) - 16 * B)]
    calc s * ((c * s + 4 * B) * (c * s - 2 * B) ^ 2) ≤ s * (c * s) ^ 3 := by gcongr
      _ = c ^ 2 * s ^ 4 * c := by ring
  -- the losses
  have l1 : w ≤ (14 / 5) * s / c := by
    rw [hw, div_le_div_iff₀ hq0 hc, hq]
    nlinarith
  have l2 : w ^ 2 * (1 / K) ≤ w := by
    have : 1 / (K : ℝ) ≤ 1 / w := one_div_le_one_div_of_le hw0 hK1
    calc w ^ 2 * (1 / K) ≤ w ^ 2 * (1 / w) := by gcongr
      _ = w := by field_simp
  have l3 : (70 / 9) * γ * w ^ 4 * Z ≤ (67228 / 1125) * s / c := by
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    calc (70 / 9) * γ * w ^ 4 * Z ≤ (70 / 9) * γ * ((14 / 5) * s / c) ^ 4 * Z := by gcongr
      _ = (67228 / 1125) * s / c := by rw [hγ, hZ]; field_simp; norm_num
  have l4 : 1 ≤ s / c := by rwa [le_div_iff₀ hc, one_mul]
  have l5 : 4 * B * s / c = 4 * B * (s / c) := by ring
  have l6 : (14 / 5) * s / c = (14 / 5) * (s / c) := by ring
  have l7 : (67228 / 1125) * s / c = (67228 / 1125) * (s / c) := by ring
  have l8 : 64 * (s / c) ≤ 4 * B * (s / c) := by
    have : (0 : ℝ) ≤ s / c := by positivity
    nlinarith
  nlinarith

/-- If the bound holds below n, and √n ≥ 7B/c + c with B ≥ 16, it holds at n. -/
theorem step {H : ℝ} {B : ℕ} (hH : 0 ≤ H) (hB : (16 : ℝ) ≤ B) {n : ℕ} (hn : 7 * (B : ℝ) / cHR + cHR ≤ Real.sqrt n)
    (ih : ∀ m, 1 ≤ m → m < n → H * Real.exp (cHR * Real.sqrt m) / (m : ℝ) ^ B ≤ p m) :
    H * Real.exp (cHR * Real.sqrt n) / (n : ℝ) ^ B ≤ p n := by
  have hZ := cHR_sq
  have hc : 0 < cHR := cHR_pos
  have hcU := cHR_bounds.2
  generalize cHR = c at *
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  rw [← hsdef] at hn ⊢
  have hs2 : s ^ 2 = n := by rw [hsdef, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hBc : 0 < 7 * (B : ℝ) / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 4 * (B : ℝ) ≤ c * s := by
    have : 7 * (B : ℝ) / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by rw [← hs2]; positivity
    exact_mod_cast this
  obtain ⟨α, hα⟩ : ∃ α, α = c / (2 * s) - B / s ^ 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = c / (2 * s ^ 3) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    have e : c / (2 * s) - B / s ^ 2 = (c * s - 2 * B) / (2 * s ^ 2) := by field_simp
    rw [hα, e]
    exact div_pos (by linarith) (by positivity)
  have hα1 : α ≤ 1 / 3 := by
    have hsc' : 3 * c / 2 ≤ s := by
      nlinarith [sq_nonneg (c - 13 / 5)]
    have h1 : c / (2 * s) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h2 : 0 ≤ (B : ℝ) / s ^ 2 := by positivity
    linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hγn : 1 ≤ γ * (s ^ 2) ^ 2 := by
    have e : γ * (s ^ 2) ^ 2 = c * s / 2 := by rw [hγ]; field_simp
    rw [e]
    linarith
  obtain ⟨K, hK⟩ : ∃ K, K = ⌈1 / α⌉₊ := ⟨_, rfl⟩
  have hw0 : 0 < 1 / α := by positivity
  have hK0 : 1 ≤ K := by rw [hK]; exact Nat.ceil_pos.2 hw0
  have hK1 : 1 / α ≤ K := by rw [hK]; exact Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 1 / α + 1 := by rw [hK]; exact (Nat.ceil_lt_add_one hw0.le).le
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (c * s) / (s ^ 2) ^ B := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  -- one term
  have term : ∀ k v : ℕ, 1 ≤ k → 1 ≤ v →
      H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) ≤ if k * v < n then (v : ℝ) * p (n - k * v) else 0 := by
    intro k v hk hv
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = k * v := ⟨_, rfl⟩
    have e1 : α * k * v = α * x := by rw [hx]; ring
    have e2 : γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2 = γ * x ^ 2 := by rw [hx]; ring
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    rw [e1, e2]
    split_ifs with h
    · have hxs : x < s ^ 2 := by rw [hs2, hx]; exact_mod_cast h
      have hr := ratio_ge B hc.le hs0 hx0 hxs
      rw [← hα, ← hγ, ← hF] at hr
      have hm : ((n - k * v : ℕ) : ℝ) = s ^ 2 - x := by rw [Nat.cast_sub h.le, hs2, hx]; push_cast; ring
      have hi := ih (n - k * v) (by omega) (Nat.sub_lt hn0 (Nat.mul_pos hk hv))
      rw [hm] at hi
      calc H * F * ((v : ℝ) * Real.exp (-(α * x)) * (1 - γ * x ^ 2)) = v * (H * (F * (Real.exp (-(α * x)) * (1 - γ * x ^ 2)))) := by ring
        _ ≤ v * (H * (Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B)) := by gcongr
        _ = v * (H * Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B) := by ring
        _ ≤ v * p (n - k * v) := by gcongr
    · have hxs : s ^ 2 ≤ x := by rw [hs2, hx]; exact_mod_cast not_lt.1 h
      have h1 : γ * (s ^ 2) ^ 2 ≤ γ * x ^ 2 := by gcongr
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  -- the sum over v for one k
  have sumv : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - (70 / 9) * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ioc.1 hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK
    refine sum_v_ge (by positivity) ?_ (by positivity) n ?_
    · calc α * k ≤ α * (1 / α + 1) := by gcongr; exact hkK'.trans hK2
        _ = 1 + α := by field_simp
        _ ≤ 4 / 3 := by linarith
    · rw [← hs2]
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
      calc 1 ≤ γ * (s ^ 2) ^ 2 := hγn
        _ = γ * 1 * (s ^ 2) ^ 2 := by ring
        _ ≤ γ * (k : ℝ) ^ 2 * (s ^ 2) ^ 2 := by gcongr
  -- the recurrence
  have hrec : ((n : ℝ) * p n) = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by exact_mod_cast mul_p_eq n
  have hmain : H * F * s ^ 2 ≤ (n : ℝ) * p n := by
    calc H * F * s ^ 2 ≤ H * F * ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - (70 / 9) * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
          gcongr
          exact (step_arith hc hB hn hα hγ hZ hK1 hK2).trans (sum_k_ge hα0 hγ0 hK0)
      _ ≤ H * F * ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
          gcongr with k hk
          exact sumv k hk
      _ = ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, if k * v < n then (v : ℝ) * p (n - k * v) else 0 :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun v hv => term k v (Finset.mem_Ioc.1 hk).1 (Finset.mem_Icc.1 hv).1
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Ioc 0 K, if k * v < n then (v : ℝ) * p (n - k * v) else 0 := Finset.sum_comm
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => by positivity
          obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
          exact Finset.mem_Icc.2 ⟨(Finset.mem_Ioc.1 hk1).1, (Nat.le_div_iff_mul_le (Finset.mem_Icc.1 hv).1).2 hk2.le⟩
      _ = (n : ℝ) * p n := hrec.symm
  rw [← hs2, mul_div_assoc, ← hF]
  rw [← hs2, mul_comm (s ^ 2)] at hmain
  exact le_of_mul_le_mul_right hmain (by positivity)

/-- The exponent 16 replaces the upstream exponent 3890. -/
theorem partition_lower_bound : ∃ H : ℝ, 0 < H ∧ ∀ E : ℕ, 1 ≤ E → H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ 16 ≤ p E := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((7 * ((16 : ℕ) : ℝ) / cHR + cHR) ^ 2)
  refine ⟨Real.exp (-(cHR * Real.sqrt n₀)), Real.exp_pos _, fun E => ?_⟩
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    rcases lt_or_ge E n₀ with h | h
    · have h1 : (1 : ℝ) ≤ p E := by exact_mod_cast p_pos E
      have h2 : (1 : ℝ) ≤ (E : ℝ) ^ 16 := one_le_pow₀ (by exact_mod_cast hE)
      have h3 : Real.sqrt E ≤ Real.sqrt n₀ := Real.sqrt_le_sqrt (by exact_mod_cast h.le)
      have h4 : Real.exp (-(cHR * Real.sqrt n₀)) * Real.exp (cHR * Real.sqrt E) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]
        have := mul_le_mul_of_nonneg_left h3 cHR_pos.le
        linarith
      refine le_trans ?_ h1
      rw [div_le_one (by positivity)]
      exact h4.trans h2
    · refine step (Real.exp_pos _).le (by norm_num) ?_ fun m hm1 hm => ih m hm hm1
      have h5 : ((7 * ((16 : ℕ) : ℝ) / cHR + cHR) ^ 2) ≤ (E : ℝ) := hn₀.trans (by exact_mod_cast h)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h5)

/-- A chord bound for log on the base interval. -/
theorem log_chord {t : ℝ} (ht : 1 ≤ t) (ht' : t ≤ 48) :
    (191 / 50) * (t - 1) / 47 ≤ Real.log t := by
  have hlog : (191 / 50 : ℝ) ≤ Real.log 48 := by
    have h : Real.log (48 : ℝ) = 6 * Real.log 2 + Real.log (3 / 4) := by
      rw [show (48 : ℝ) = 2 ^ 6 * (3 / 4) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [h]
    have hfrac := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
    norm_num at hfrac
    linarith [Real.log_two_gt_d9]
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (48 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ (48 - t) / 47 by linarith)
    (show 0 ≤ (t - 1) / 47 by linarith)
    (show (48 - t) / 47 + (t - 1) / 47 = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  have he : (48 - t) / 47 * 1 + (t - 1) / 47 * 48 = t := by ring
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (t - 1) / 47 by linarith)
  linarith

/-- A completely explicit lower bound, with no small exponential prefactor loss. -/
theorem explicit_partition_lower_bound (E : ℕ) (hE : 1 ≤ E) :
    Real.exp (-3) * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ 16 ≤ p E := by
  obtain ⟨hcL, hcU⟩ := cHR_bounds
  have hs48 : Real.sqrt (2304 : ℝ) = 48 := by norm_num
  have hcut : 7 * (16 : ℝ) / cHR + cHR ≤ 48 := by
    have hdiv : (7 * (16 : ℝ)) / cHR ≤ 112 / (5 / 2) := by
      calc
        (7 * (16 : ℝ)) / cHR = 112 / cHR := by norm_num
        _ ≤ 112 / (5 / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hcL
    linarith only [hdiv, hcU]
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases lt_or_ge E 2304 with h | h
    · have h1 : (1 : ℝ) ≤ p E := by exact_mod_cast p_pos E
      have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
      have hs : Real.sqrt E ≤ 48 := by
        rw [← hs48]
        exact Real.sqrt_le_sqrt (by exact_mod_cast h.le)
      have hs1 : 1 ≤ Real.sqrt (E : ℝ) := by
        exact (Real.le_sqrt (by norm_num) hE0.le).2 (by exact_mod_cast hE)
      have hc := mul_le_mul_of_nonneg_right hcU (Real.sqrt_nonneg (E : ℝ))
      have hlog := log_chord hs1 hs
      have hlogE : Real.log (E : ℝ) = 2 * Real.log (Real.sqrt E) := by
        rw [Real.log_sqrt hE0.le]
        ring
      have hexp : -3 + cHR * Real.sqrt E ≤ 16 * Real.log (E : ℝ) := by
        rw [hlogE]
        nlinarith only [hc, hlog, hs1]
      have h4 : Real.exp (-3) * Real.exp (cHR * Real.sqrt E) ≤ (E : ℝ) ^ 16 := by
        rw [← Real.exp_add, ← Real.exp_log (pow_pos hE0 16), Real.log_pow]
        exact Real.exp_le_exp.mpr hexp
      exact (div_le_one (pow_pos hE0 16)).mpr h4 |>.trans h1
    · apply step (Real.exp_pos _).le (by norm_num)
      · exact hcut.trans (by rw [← hs48]; exact Real.sqrt_le_sqrt (by exact_mod_cast h))
      · intro m hm hmn
        exact ih m hmn hm

end ETHConstants.Partition
