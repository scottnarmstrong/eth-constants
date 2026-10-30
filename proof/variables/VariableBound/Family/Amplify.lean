/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import AppVariablesStatement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! XOR amplification of a family of parity checks. -/
@[expose] public section
namespace VariableBound.Amplify
open Finset
variable {E ι : Type} [Fintype E] [DecidableEq E] [Fintype ι]

def triple (S T U : Finset E) : Finset E :=
  univ.filter fun e => Xor (e ∈ S) (Xor (e ∈ T) (e ∈ U))

def sign (S V : Finset E) : ℤ := (-1) ^ #(S ∩ V)

theorem sign_eq_prod (S V : Finset E) :
    sign S V = ∏ e : E, if e ∈ S ∧ e ∈ V then (-1:ℤ) else 1 := by
  rw [← prod_filter]
  have h : (univ.filter fun e : E => e ∈ S ∧ e ∈ V) = S ∩ V := by ext; simp
  rw [h, prod_const]
  rfl

theorem sign_triple (S T U V : Finset E) :
    sign (triple S T U) V = sign S V * sign T V * sign U V := by
  simp only [sign_eq_prod, ← prod_mul_distrib]
  apply prod_congr rfl
  intro e _
  by_cases hs : e ∈ S <;> by_cases ht : e ∈ T <;>
    by_cases hu : e ∈ U <;> by_cases hv : e ∈ V <;> simp [triple, Xor, hs, ht, hu, hv]

omit [Fintype E] in
theorem sum_sign (Γ : ι → Finset E) (V : Finset E) :
    ∑ i, sign (Γ i) V = (Fintype.card ι : ℤ) - 2 * #{i : ι | Odd #(Γ i ∩ V)} := by
  have h (i : ι) : sign (Γ i) V = 1 - 2 * (if Odd #(Γ i ∩ V) then (1:ℤ) else 0) := by
    unfold sign
    rw [neg_one_pow_eq_ite]
    by_cases hh : Even #(Γ i ∩ V) <;> simp [hh, ← Nat.not_even_iff_odd]
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum, sum_boole]
  simp

theorem sum_sign_triple (Γ : ι → Finset E) (V : Finset E) :
    ∑ i : ι × ι × ι, sign (triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)) V =
      (∑ i, sign (Γ i) V)^3 := by
  simp only [sign_triple, Fintype.sum_prod_type]
  simp_rw [← mul_sum, ← sum_mul]
  simp_rw [← mul_sum, ← sum_mul]
  ring

/-- A detection probability at least 1/4 becomes at least 7/16 after three XORs. -/
theorem odd_triple (Γ : ι → Finset E) (V : Finset E)
    (h : Fintype.card ι ≤ 4 * #{i : ι | Odd #(Γ i ∩ V)}) :
    7 * Fintype.card (ι × ι × ι) ≤
      16 * #{i : ι × ι × ι | Odd #(triple (Γ i.1) (Γ i.2.1) (Γ i.2.2) ∩ V)} := by
  have hs := sum_sign Γ V
  have ht := sum_sign (fun i : ι × ι × ι => triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)) V
  rw [sum_sign_triple, hs] at ht
  have hR : (Fintype.card ι : ℤ) ≤ 4 * #{i : ι | Odd #(Γ i ∩ V)} := by exact_mod_cast h
  have hc : (Fintype.card (ι × ι × ι) : ℤ) = (Fintype.card ι : ℤ)^3 := by
    simp only [Fintype.card_prod, Nat.cast_mul]; ring
  rw [hc] at ht
  have hh : 2 * ((Fintype.card ι : ℤ) - 2 * #{i : ι | Odd #(Γ i ∩ V)}) ≤ Fintype.card ι := by omega
  have hp := (Odd.strictMono_pow (by decide : Odd 3)).monotone hh
  have he : (2 * ((Fintype.card ι : ℤ) - 2 * #{i : ι | Odd #(Γ i ∩ V)}))^3 =
      8 * ((Fintype.card ι : ℤ) - 2 * #{i : ι | Odd #(Γ i ∩ V)})^3 := by ring
  rw [he, ht] at hp
  have hh' : 7 * (Fintype.card (ι × ι × ι) : ℤ) ≤
      16 * #{i : ι × ι × ι | Odd #(triple (Γ i.1) (Γ i.2.1) (Γ i.2.2) ∩ V)} := by
    rw [hc]
    linarith only [hp]
  exact_mod_cast hh'

theorem card_triple_le (S T U : Finset E) : #(triple S T U) ≤ #S + #T + #U := by
  have hh : triple S T U ⊆ (S ∪ T) ∪ U := by
    intro e he
    have he' := (mem_filter.mp he).2
    simp only [Xor] at he'
    simp only [mem_union]
    tauto
  exact (card_le_card hh).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))

theorem incidence_triple_le (Γ : ι → Finset E) (e : E) :
    #{i : ι × ι × ι | e ∈ triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)} ≤
      3 * #{i : ι | e ∈ Γ i} * Fintype.card ι ^ 2 := by
  classical
  let A : Finset ι := univ.filter fun i => e ∈ Γ i
  have hs : (univ.filter fun i : ι × ι × ι => e ∈ triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)) ⊆
      ((A ×ˢ univ) ∪ (univ ×ˢ (A ×ˢ univ))) ∪ (univ ×ˢ (univ ×ˢ A)) := by
    intro i hi
    have ht : e ∈ triple (Γ i.1) (Γ i.2.1) (Γ i.2.2) := (Finset.mem_filter.mp hi).2
    have hi' := (Finset.mem_filter.mp ht).2
    simp only [Xor] at hi'
    simp only [mem_union, mem_product, mem_univ, true_and, and_true, A, mem_filter]
    tauto
  calc
    _ ≤ #(((A ×ˢ univ) ∪ (univ ×ˢ (A ×ˢ univ))) ∪ (univ ×ˢ (univ ×ˢ A))) := card_le_card hs
    _ ≤ #(A ×ˢ (univ : Finset (ι × ι))) + #(univ ×ˢ (A ×ˢ (univ : Finset ι))) +
        #((univ : Finset ι) ×ˢ ((univ : Finset ι) ×ˢ A)) :=
      (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
    _ = _ := by simp only [card_product, card_univ, Fintype.card_prod]; dsimp [A]; ring

/-- Three XORs enlarge the checks and each incidence bound by at most three. -/
theorem triple_bounds {v : ℕ} (Γ : ι → Finset E)
    (h : AppVariables.BaseFamily v univ Γ) :
    (∀ i : ι × ι × ι, v * #(triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)) ≤ 48 * Fintype.card E) ∧
    (∀ e : E, 15 * v * #{i : ι × ι × ι | e ∈ triple (Γ i.1) (Γ i.2.1) (Γ i.2.2)} ≤
      48 * Fintype.card (ι × ι × ι)) ∧
    (∀ V : Finset E, v < #V → 7 * Fintype.card (ι × ι × ι) ≤
      16 * #{i : ι × ι × ι | Odd #(triple (Γ i.1) (Γ i.2.1) (Γ i.2.2) ∩ V)}) := by
  refine ⟨fun i => ?_, fun e => ?_, fun V hV => odd_triple Γ V (by simpa using h.c V hV)⟩
  · have h1 := h.a i.1 (mem_univ _)
    have h2 := h.a i.2.1 (mem_univ _)
    have h3 := h.a i.2.2 (mem_univ _)
    have hc := Nat.mul_le_mul_left v (card_triple_le (Γ i.1) (Γ i.2.1) (Γ i.2.2))
    nlinarith only [h1, h2, h3, hc]
  · have hb := h.b e
    rw [card_univ] at hb
    have h1 := Nat.mul_le_mul_left (15*v) (incidence_triple_le Γ e)
    have h2 := Nat.mul_le_mul_right (3 * Fintype.card ι ^ 2) hb
    simp only [Fintype.card_prod]
    nlinarith only [h1, h2]

end VariableBound.Amplify
