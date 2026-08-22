/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ReflectionCore
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.DeriveFintype

/-!
# Lightweight executable core of the residual E7 shell

This module contains the five residual orbit types, their canonical
representatives, and the finite eligible-shell predicate.  It deliberately
excludes packing and transport proofs so certificate audits can regenerate
shell cardinalities with a small import footprint.
-/

namespace SRG266

/-- The five orbit-pair types left by the supplied centroid certificate. -/
inductive E7ResidualType
  | twoTen
  | fourEightGeneric
  | fourEightSpecial
  | sixGenericSixGeneric
  | sixGenericSixSpecial
  deriving DecidableEq, Fintype

/-- Canonical doubled-coordinate representatives for the seven component
orbits occurring in the five residual types. -/
def e7ResidualCanonical :
    E7ResidualType → (Fin 8 → ℤ) × (Fin 8 → ℤ)
  | .twoTen =>
      (![-2, 0, 0, 0, 0, 0, 0, 2],
       ![-5, -1, -1, 1, 1, 1, 1, 3])
  | .fourEightGeneric =>
      (![-3, -1, -1, 1, 1, 1, 1, 1],
       ![-5, -1, 1, 1, 1, 1, 1, 1])
  | .fourEightSpecial =>
      (![-3, -1, -1, 1, 1, 1, 1, 1],
       ![-4, 0, 0, 0, 0, 0, 0, 4])
  | .sixGenericSixGeneric =>
      (![-4, 0, 0, 0, 0, 0, 2, 2],
       ![-4, 0, 0, 0, 0, 0, 2, 2])
  | .sixGenericSixSpecial =>
      (![-4, 0, 0, 0, 0, 0, 2, 2],
       ![-3, -3, 1, 1, 1, 1, 1, 1])

/-- Evaluation of a minuscule weight against doubled `E₇` coordinates. -/
def e7ResidualEvaluation
    (d : Fin 8 → ℤ) (w : E7WeightIndex) : ℤ :=
  integerDot d (e7Weight4 w) / 8

/-- Twice the inner product of two minuscule weights. -/
def e7WeightPairing2 (u v : E7WeightIndex) : ℤ :=
  integerDot (e7Weight4 u) (e7Weight4 v) / 8

/-- Inner product of two norm-three vectors in the paired minuscule shell. -/
def e7ShellInner (u v : E7ShellIndex) : ℤ :=
  (e7WeightPairing2 u.1 v.1 + e7WeightPairing2 u.2 v.2) / 2

/-- Eligibility for the residual centroid `d = c / 5`. -/
def e7ResidualEligible
    (d₁ d₂ : Fin 8 → ℤ) (w : E7ShellIndex) : Prop :=
  e7ResidualEvaluation d₁ w.1 + e7ResidualEvaluation d₂ w.2 = 3

instance (d₁ d₂ : Fin 8 → ℤ) :
    DecidablePred (e7ResidualEligible d₁ d₂) :=
  fun w => by
    unfold e7ResidualEligible
    infer_instance

/-- Eligible paired minuscule weights for a residual centroid. -/
abbrev E7ResidualEligibleIndex
    (d₁ d₂ : Fin 8 → ℤ) :=
  {w : E7ShellIndex // e7ResidualEligible d₁ d₂ w}

instance (d₁ d₂ : Fin 8 → ℤ) :
    Fintype (E7ResidualEligibleIndex d₁ d₂) :=
  Fintype.subtype
    (Finset.univ.filter (e7ResidualEligible d₁ d₂))
    (by simp)

end SRG266
