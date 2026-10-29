/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ExplicitPieces
public import WitnessExtraction
public import PiecesCounted.Padded
public import PiecesCounted.PaddedData
public import PiecesCounted.Basic
public import PiecesCounted.Assume
public import CountedRecursion.Main
import all CountedRecursion.Base
import all CountedRecursion.BothNetworks
import all CountedRecursion.CallLemma
import all CountedRecursion.CountStep
import all CountedRecursion.EndCounted
import all CountedRecursion.EndPlugged
import all CountedRecursion.EndSolves
import all CountedRecursion.Main
import all CountedRecursion.Meets
import all CountedRecursion.Numbers
import all CountedRecursion.ProcedureCost
import all CountedRecursion.RoomWithin
import all CountedRecursion.SolverCall
import all CountedRecursion.SolverRoom
import all CountedRecursion.SolverStep
import all CountedRecursion.TotalCount
import all CountedRecursion.TotalRoom
import all ExplicitCost.Cost
import all ExplicitCost.GroupingCall
import all ExplicitCost.GroupingSearch

/-! Connect the numerical piece constants to the existing counted recursion. -/

@[expose] public section

namespace ETHConstants.ExplicitRecursion

open Groundwork Groundwork.Prog PiecesCounted Real ClauseBound.Inst.Half

noncomputable def data : Data :=
  ofPadded (halfF 2 95) GeneralPieces.halfA 190 (fun _ => 0)

def algorithm : Stepped (List Unit × Question) Answer :=
  algOf (halfF 2 95) (GeneralPieces.valOf (halfF 2 95)) 190 (fun _ => 0)

theorem data_is : data.Is (1 / √2) 190 := by
  apply ofPadded_is ExplicitPieces.isPieces
  intro lam _
  simp only [abs_zero, zero_add]
  exact_mod_cast (Nat.lt_two_pow_self (n := (2 * lam) ^ 190) :
    (2 * lam) ^ 190 < 2 ^ (2 * lam) ^ 190)

/-- The constant for the untrimmed counted piece algorithm is 191. -/
theorem pieces : IsPieces (1 / √2) 191 data algorithm := by
  refine ⟨data_is.grow le_rfl ExplicitPieces.isPieces.rho_lt (by norm_num),
    algOf_polyT ExplicitPieces.isPieces (by fun_prop) 190, ?_⟩
  exact computes_of_answer data_is (k := 190) le_rfl (by norm_num) (by norm_num)
    (fun _ _ hg => answerOf_eq ExplicitPieces.isPieces hg)

noncomputable def shortData : Data := trimmed data

def shortAlgorithm : Stepped (List Unit × Question) Answer := assumeAlg algorithm

/-- Trimming to at most 2λ bits costs two in the counted parameter. -/
theorem shortPieces : IsPieces (1 / √2) 193 shortData shortAlgorithm :=
  ⟨(trimmed_is pieces.is).grow le_rfl pieces.is.rho_lt (by norm_num),
    assumeAlg_polyT pieces.polyTimeSteps, assume_computes pieces.is pieces.computes⟩

/-- The strengthened recursion admits starting exponent sixteen. -/
theorem setting : ExplicitCost.Setting (1 / √2) 193 16 shortData := by
  refine ⟨shortPieces.is, fun lam tr i => ?_, le_rfl, by norm_num⟩
  exact (trimmed_cap data lam tr i).trans_le (min_le_right _ _)

/-- Extract the actual numerical witness from the constructive upstream proof.
The kernel checks that the witness really is 61515. -/
theorem recursionConstant : ∀ (ρ : ℝ) (x₀ : ℕ) (D : Data)
    (Alg : Stepped ExplicitCost.PieceQuery ExplicitCost.Ans),
    IsPieces ρ 193 D Alg → ExplicitCost.Setting ρ 193 x₀ D →
    (ExplicitCost.cliqueMachine 193 x₀ Alg).PolyTimeSteps ∧
    CliqueLevels.Solves (ExplicitCost.cliqueMachine 193 x₀ Alg)
      (Levels.Gen.K x₀) (Levels.Gen.e ρ x₀) 61515 := by
  extract_exists_body (ExplicitCost.recursionSolves 193)

/-- A closed correctness and numerical counted-cost theorem for the new instantiation. -/
theorem solves :
    (ExplicitCost.cliqueMachine 193 16 shortAlgorithm).PolyTimeSteps ∧
    CliqueLevels.Solves (ExplicitCost.cliqueMachine 193 16 shortAlgorithm)
      (Levels.Gen.K 16) (Levels.Gen.e (1 / √2) 16) 61515 :=
  recursionConstant (1 / √2) 16 shortData shortAlgorithm shortPieces setting

end ETHConstants.ExplicitRecursion
