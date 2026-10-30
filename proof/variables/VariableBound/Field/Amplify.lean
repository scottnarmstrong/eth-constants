/-
Copyright (c) 2026 Anthropic, PBC; Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import VariableBound.Field.Main
public import VariableBound.Family.Amplify
import Mathlib.Tactic

public section
namespace VariableBound.Fld
open Groundwork Finset

theorem ampFamily_comap {E ι ι' : Type} [Fintype E] [DecidableEq E] {v : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (h : AppVariables.IsFamily v Ω Γ)
    (φ : ι' ↪ ι) (Ω' : Finset ι') (hΩ : Ω = Ω'.map φ) : AppVariables.IsFamily v Ω' fun i => Γ (φ i) := by
  subst hΩ
  refine ⟨fun u hu => h.a _ (Finset.mem_map_of_mem φ hu), fun e => ?_, fun V hV => ?_⟩
  · have := h.b e
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this
  · have := h.c V hV
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this

/-- Let the list L have no repetitions, let D be injective on its members with image Ω, and let G u
list the set Γ (D u) for every member u of L. If the sets Γ_w, w ∈ Ω, have (a), (b), (c) of
Lemma 13 (Family of checks) for v, then the list `L.map G` has |Ω| members, and they, indexed by
their places, have (a), (b), (c) for v. -/
theorem ampFamily_list {m v : ℕ} {ι U : Type} (Ω : Finset ι) (Γ : ι → Finset (Fin m)) (L : List U) (D : U → ι) (G : U → List ℕ)
    (hL : L.Nodup) (hD : ∀ u ∈ L, ∀ u' ∈ L, D u = D u' → u = u') (hΩ : ∀ w, w ∈ Ω ↔ ∃ u ∈ L, D u = w)
    (hG : ∀ u ∈ L, setD m (G u) = Γ (D u)) (h : AppVariables.IsFamily v Ω Γ) :
    #Ω = (L.map G).length ∧ AppVariables.IsFamily v (univ : Finset (Fin (L.map G).length)) fun i => setD m ((L.map G).get i) := by
  have hlen : (L.map G).length = L.length := List.length_map G
  let φ : Fin (L.map G).length ↪ ι := ⟨fun i => D (L.get (i.cast hlen)), fun i j hij => by
    have := hD _ (List.get_mem L _) _ (List.get_mem L _) hij
    have := (List.Nodup.get_inj_iff hL).1 this
    exact Fin.cast_injective hlen this⟩
  have hmap : Ω = (univ : Finset (Fin (L.map G).length)).map φ := by
    ext w
    rw [hΩ, Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hu
      exact ⟨i.cast hlen.symm, Finset.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      exact ⟨_, List.get_mem L _, rfl⟩
  refine ⟨by rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin], ?_⟩
  have key := ampFamily_comap h φ univ hmap
  have e : (fun i : Fin (L.map G).length => setD m ((L.map G).get i)) = fun i => Γ (φ i) := by
    funext i
    have : (L.map G).get i = G (L.get (i.cast hlen)) := by simp
    rw [this, hG _ (List.get_mem L _)]
    rfl
  rw [e]
  exact key

theorem setD_xorChecks (m : ℕ) (p : List ℕ × List ℕ × List ℕ) :
    setD m (xorChecks m p) = Amplify.triple (setD m p.1) (setD m p.2.1) (setD m p.2.2) := by
  ext e
  by_cases h1 : e.val ∈ p.1 <;> by_cases h2 : e.val ∈ p.2.1 <;>
    by_cases h3 : e.val ∈ p.2.2 <;> simp [setD, xorChecks, Amplify.triple, Xor, h1, h2, h3]

/-- Listing threefold XORs is still polynomial-time. -/
theorem famAmpD_poly : StCertFamAmpD := by
  intro α _ m a hm ha
  have hf := Cert.stCertFamD α m a hm ha
  unfold famAmpD xorChecks
  fun_prop

/-- The executable list enumerates exactly all triple XORs. -/
theorem famAmpD_eq (m a : ℕ) :
    famAmpD m a =
      (List.finRange (famD m a).length ×ˢ List.finRange (famD m a).length ×ˢ
        List.finRange (famD m a).length).map fun i =>
          xorChecks m ((famD m a).get i.1, (famD m a).get i.2.1, (famD m a).get i.2.2) := by
  dsimp only [famAmpD]
  generalize famD m a = f
  simp only [← List.map_coe_finRange_eq_range]
  simp only [SProd.sprod, List.product, List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  funext k
  simp

/-- The amplified, executable family has the stronger detection guarantee. -/
theorem famAmpD_isFamily : StFamAmpD := by
  classical
  intro m a ha hm
  have hb := famD_isFamily m a ha hm
  let f := famD m a
  let I := Fin f.length × Fin f.length × Fin f.length
  let L := List.finRange f.length ×ˢ List.finRange f.length ×ˢ List.finRange f.length
  let G : I → List ℕ := fun i => xorChecks m (f.get i.1, f.get i.2.1, f.get i.2.2)
  let Γ : I → Finset (Fin m) := fun i =>
    Amplify.triple (setD m (f.get i.1)) (setD m (f.get i.2.1)) (setD m (f.get i.2.2))
  have hΓ : AppVariables.IsFamily (2^a) univ Γ := by
    obtain ⟨h1, h2, h3⟩ := Amplify.triple_bounds (fun i => setD m (f.get i)) hb.2.2.2
    exact ⟨fun i _ => by simpa [Γ] using h1 i, by simpa [Γ, I] using h2, by simpa [Γ, I] using h3⟩
  have he : famAmpD m a = L.map G := famAmpD_eq m a
  have ht := ampFamily_list univ Γ L id G
    ((List.nodup_finRange _).product ((List.nodup_finRange _).product (List.nodup_finRange _)))
    (fun _ _ _ _ h => h) (fun w => by
      rcases w with ⟨i, j, k⟩
      simp [L, List.mem_product, List.mem_finRange])
    (fun u _ => setD_xorChecks m _) hΓ
  have hlen : (famAmpD m a).length = f.length^3 := by
    rw [he, ← ht.1]
    simp only [card_univ, I, Fintype.card_prod, Fintype.card_fin]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpos : 0 < f.length := List.length_pos_iff.mpr hb.1
    intro hh
    rw [hh, List.length_nil] at hlen
    have : 0 < f.length^3 := pow_pos hpos _
    omega
  · rw [hlen]
    calc
      _ < ((32*m)^4)^3 := Nat.pow_lt_pow_left hb.2.1 (by decide)
      _ = (32*m)^12 := by rw [← pow_mul]
  · intro l hl
    rw [he] at hl
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hl
    refine ⟨List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range,
      List.Nodup.sublist List.filter_sublist List.nodup_range, ?_⟩
    exact fun E hE => List.mem_range.mp (List.mem_of_mem_filter hE)
  · rw [he]
    exact ht.2

end VariableBound.Fld
