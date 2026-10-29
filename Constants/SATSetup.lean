/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ExplicitPieces
public import WitnessExtraction
public import SharperSchedule
public import RecursionWithPieces.Master
public import VariableBound.MainPrinted
public import VariableBound.Top.ArithNat
public import VariableBound.Top.ArithPlan
import all GeneralPieces.Rec.Rate

@[expose] public section
namespace ETHConstants.SAT
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
open GeneralPieces ClauseBound.Inst.Half ClauseBound.Gen.Seq AppRunningTime

noncomputable abbrev rho : ℝ := 1 / Real.sqrt 2

def pieces : PiecesF := Tied.recOf (halfF 2 95) (GeneralPieces.valOf (halfF 2 95)) 190

def solver := solverOf pieces

def pick := Pick.pick pieces 16

theorem parameters : Par pieces rho 190 ∧ pieces.Keeps ∧ pieces.m = 1 :=
  par_of_isPieces ExplicitPieces.isPieces

theorem rho_ge : (1 / 2 : ℝ) ≤ rho := ExplicitPieces.isPieces.rho_ge
theorem rho_lt : rho < 1 := ExplicitPieces.isPieces.rho_lt

theorem rho_sq : rho ^ 2 = 1 / 2 := by
  simp [rho, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem rho_le : rho ≤ 3 / 4 := by
  nlinarith [rho_sq, rho_ge]

theorem partA : PartA.TheoremAa rho 16 := PartA.thmRunningTime_a rho 16 rho_ge rho_lt le_rfl

theorem rateConstant : ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ),
    1 / 2 ≤ ρ → ρ < 1 → Par P ρ 190 → P.m = 1 → 16 ≤ x₀ → 190 + 5 ≤ 2 ^ x₀ →
    ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
      (needG P (K x₀ l) lam B 1 1 (sched P x₀ l) : ℝ) ≤
        e ρ x₀ l * (K x₀ l : ℝ)^2 * lam +
        1157 * (K x₀ l : ℝ)^2 * Real.logb 2 (K x₀ l * (lam + B)) := by
  extract_exists_body (GeneralPieces.stRate2 190)

theorem solver_poly : solver.Poly := GeneralPieces.solver_poly pieces parameters.2.1

theorem solver_K (l : ℕ) : solver.K (idx pieces 16 l) = K 16 l := topK_idx pieces 16 l

theorem solver_rate (l lam B : ℕ) (hlam : 1 ≤ lam) (hB : 1 ≤ B) :
    (solver.need (idx pieces 16 l, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e rho 16 l * (K 16 l : ℝ)^2 * lam +
      1157 * (K 16 l : ℝ)^2 * Real.logb 2 (K 16 l * (lam + B)) := by
  have h := rateConstant pieces rho 16 rho_ge rho_lt parameters.1 parameters.2.2
    le_rfl (by norm_num) l lam B hlam hB
  simp only [solver, solverOf, List.length_replicate, topK_idx]
  simpa only [idx] using h

end ETHConstants.SAT
