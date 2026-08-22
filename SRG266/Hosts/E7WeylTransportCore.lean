/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ReflectionCore

/-!
# Lightweight executable core of E7 Weyl transport

This module contains only the finite weight reflection and its Boolean
checker.  It imports neither residual-shell elimination nor Gram-realization
theory, allowing mined reflection certificates to be checked in isolation.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- Cleared coordinate formula saying that `v` is the reflection of `u`
through the root `a`. -/
def e7WeightReflects
    (a : Fin 8 → ℤ) (u v : E7WeightIndex) : Prop :=
  ∀ i, 4 * e7Weight4 v i =
    4 * e7Weight4 u i - integerDot (e7Weight4 u) a * a i

instance (a : Fin 8 → ℤ) (u v : E7WeightIndex) :
    Decidable (e7WeightReflects a u v) := by
  unfold e7WeightReflects
  infer_instance

/-- Canonical computable enumeration of the 56 signed minuscule weights. -/
def e7WeightData : List E7WeightIndex :=
  [false, true].flatMap fun sign =>
    (List.finRange e7Pairs.length).map fun pair => (sign, pair)

/-- Search the complete 56-weight shell for the reflected weight. -/
def e7ReflectedWeight
    (a : Fin 8 → ℤ) (u : E7WeightIndex) : E7WeightIndex :=
  (e7WeightData.find? fun v => decide (e7WeightReflects a u v)).getD u

/-- Check a root and its induced self-inverse permutation of all 56
minuscule weights. -/
def e7ReflectionTransportCheck (a : Fin 8 → ℤ) : Bool :=
  e7IsRoot a &&
    decide (
      (∀ u, e7WeightReflects a u (e7ReflectedWeight a u)) ∧
      ∀ u, e7ReflectedWeight a (e7ReflectedWeight a u) = u)

end SRG266
