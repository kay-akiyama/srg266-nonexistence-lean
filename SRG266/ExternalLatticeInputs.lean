/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.EmbeddingReduction
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Explicit external rank-15 lattice inputs

This file records the Yang--Yoshino embedding input and the strong final-case
reduction input.

`YangYoshinoRank15Embedding` produces a pairing-preserving embedding of the
abstract local Gram lattice into a positive-definite odd unimodular integral
lattice of rank 15.

`Rank15FinalCaseReductionInput` carries an embedded witness to one of the
checked standard-host cases.
-/

namespace SRG266

universe u

/-- A positive-definite odd unimodular integral lattice of rank 15.

The carrier is explicitly finite and free over `ℤ`, matching the standard
classical definition.  It is bundled as a `ModuleCat` so its additive and
integer-module instances remain available in all dependent fields.
Unimodularity is stated as bijectivity of the adjoint map to the integral
dual. -/
structure OddUnimodularLattice15 where
  carrier : ModuleCat ℤ
  [moduleFree : Module.Free ℤ carrier]
  [moduleFinite : Module.Finite ℤ carrier]
  pairing : LinearMap.BilinForm ℤ carrier
  symmetric : pairing.IsSymm
  positiveDefinite :
    ∀ v : carrier, v ≠ 0 → 0 < pairing v v
  odd : ∃ v : carrier, ¬Even (pairing v v)
  unimodular : Function.Bijective pairing
  rank : Module.finrank ℤ carrier = 15

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact output object of the Yang--Yoshino embedding theorem. -/
structure Rank15EmbeddingWitness (x : V) where
  host : OddUnimodularLattice15
  embedding :
    IntegralGramLattice G x →ₗ[ℤ] host.carrier
  injective : Function.Injective embedding
  preservesPairing :
    ∀ a b,
      host.pairing (embedding a) (embedding b) =
        integralGramPairing G x a b

/-- Named external input: the local integral Gram lattice embeds in an odd
unimodular positive-definite lattice of rank 15. -/
abbrev YangYoshinoRank15Embedding : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsHypothetical G → ∀ x : V,
      Nonempty (Rank15EmbeddingWitness G x)

/-- Reduction of an embedded local Gram lattice to a checked coordinate
case. -/
abbrev Rank15FinalCaseReductionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V),
    Rank15EmbeddingWitness G x → Nonempty (Rank15HostCase G x)

/-- The two named external lattice inputs imply the bundled host reduction. -/
theorem rank15HostReduction_of_external_inputs
    (hYY : YangYoshinoRank15Embedding.{u})
    (hClass : Rank15FinalCaseReductionInput.{u}) :
    Rank15HostReduction.{u} := by
  intro V _ _ G _ hG x
  obtain ⟨embedding⟩ := hYY G hG x
  exact hClass G hG x embedding

end SRG266
