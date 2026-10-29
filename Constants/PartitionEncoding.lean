/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PartitionStatement
public import ClauseBound.Part.Bits
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! An explicit injection of λ-bit strings into partitions of 2λ². A subset
of {2,...,λ+1} is recorded by those parts, and ones fill the remaining weight.
This removes the asymptotic partition estimate from the bound on h(λ). -/

@[expose] public section

namespace ETHConstants.PartitionEncoding

open Finset

def selectedParts {lam : ℕ} (s : Finset (Fin lam)) : Multiset ℕ :=
  s.val.map fun i => i.val + 2

theorem selectedParts_sum_le {lam : ℕ} (hl : 1 ≤ lam) (s : Finset (Fin lam)) :
    (selectedParts s).sum ≤ 2 * lam ^ 2 := by
  have hsum : (selectedParts s).sum = ∑ i ∈ s, (i.val + 2) := rfl
  have hc : s.card ≤ lam := (Finset.card_le_univ s).trans_eq (by simp)
  calc
    (selectedParts s).sum = ∑ i ∈ s, (i.val + 2) := hsum
    _ ≤ ∑ _i ∈ s, (lam + 1) := Finset.sum_le_sum fun i _ => by omega
    _ = s.card * (lam + 1) := by simp
    _ ≤ lam * (lam + 1) := Nat.mul_le_mul_right _ hc
    _ ≤ 2 * lam ^ 2 := by nlinarith

def subsetPartition {lam : ℕ} (hl : 1 ≤ lam) (s : Finset (Fin lam)) :
    Nat.Partition (2 * lam ^ 2) where
  parts := selectedParts s + Multiset.replicate (2 * lam ^ 2 - (selectedParts s).sum) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
      omega
    · have := (Multiset.mem_replicate.mp hi).2
      omega
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    exact Nat.add_sub_of_le (selectedParts_sum_le hl s)

theorem mem_subsetPartition {lam : ℕ} (hl : 1 ≤ lam) (s : Finset (Fin lam))
    (i : Fin lam) : i.val + 2 ∈ (subsetPartition hl s).parts ↔ i ∈ s := by
  change i.val + 2 ∈ selectedParts s + Multiset.replicate _ 1 ↔ i ∈ s
  constructor
  · intro hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · obtain ⟨j, hj, he⟩ := Multiset.mem_map.mp hi
      have hji : j = i := Fin.ext (by omega)
      simpa only [hji, Finset.mem_val] using hj
    · have := (Multiset.mem_replicate.mp hi).2
      omega
  · intro hi
    exact Multiset.mem_add.mpr (.inl (Multiset.mem_map.mpr ⟨i, hi, rfl⟩))

theorem subsetPartition_injective {lam : ℕ} (hl : 1 ≤ lam) :
    Function.Injective (subsetPartition hl) := by
  intro s t h
  apply Finset.ext
  intro i
  rw [← mem_subsetPartition hl s i, ← mem_subsetPartition hl t i, h]

/-- Every λ-bit word can be encoded at weight 2λ², for λ ≥ 1. -/
theorem two_pow_le_partitions (lam : ℕ) (hl : 1 ≤ lam) :
    2 ^ lam ≤ Partitions.p (2 * lam ^ 2) := by
  calc
    2 ^ lam = Fintype.card (Finset (Fin lam)) := by simp
    _ ≤ Fintype.card (Nat.Partition (2 * lam ^ 2)) :=
      Fintype.card_le_of_injective (subsetPartition hl) (subsetPartition_injective hl)
    _ = Partitions.p (2 * lam ^ 2) := rfl

/-- The actual least partition weight used by the programs has constant two. -/
theorem hOf_le (lam : ℕ) (hl : 1 ≤ lam) :
    ClauseBound.Part.hOf lam ≤ 2 * lam ^ 2 := by
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ ⟨by nlinarith, two_pow_le_partitions lam hl⟩

end ETHConstants.PartitionEncoding
