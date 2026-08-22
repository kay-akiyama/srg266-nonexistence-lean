/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.IntegerDot
import Mathlib.Data.Fintype.Prod

/-!
# Lightweight finite E7 weight model

This module contains the exact 56-element minuscule-weight model used by the
executable E7 certificate checkers, without importing centroid or Farkas
theory.
-/

namespace SRG266

/-- The 28 unordered pairs of an eight-element coordinate set, in the
lexicographic order used by the certificate generator. -/
def e7Pairs : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
   (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
   (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
   (3, 4), (3, 5), (3, 6), (3, 7),
   (4, 5), (4, 6), (4, 7),
   (5, 6), (5, 7),
   (6, 7)]

/-- An index for one of the 28 positive minuscule weights. -/
abbrev E7PairIndex := Fin e7Pairs.length

/-- A signed minuscule weight.  The Boolean chooses one of the two signs. -/
abbrev E7WeightIndex := Bool × E7PairIndex

/-- A pair of minuscule weights, one in each `E₇` factor. -/
abbrev E7ShellIndex := E7WeightIndex × E7WeightIndex

/-- Four times a minuscule `E₇` weight. -/
def e7Weight4 (w : E7WeightIndex) (k : Fin 8) : ℤ :=
  let p := e7Pairs.get w.2
  let z : ℤ := if k = p.1 ∨ k = p.2 then 3 else -1
  if w.1 then -z else z

end SRG266
