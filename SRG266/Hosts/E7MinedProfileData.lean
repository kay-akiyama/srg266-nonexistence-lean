/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7MinedNormSearch

/-! # Explicit output profiles of the mined E7 norm search -/

namespace SRG266

/-- Canonical normal form of the 25 divided E7 component profiles. -/
def e7MinedNormProfileData : List (List ℤ) :=
  [ [-5, -1, -1, 1, 1, 1, 1, 3],
    [-5, -1, 1, 1, 1, 1, 1, 1],
    [-4, -2, -2, 0, 2, 2, 2, 2],
    [-4, -2, 0, 0, 0, 0, 2, 4],
    [-4, -2, 0, 0, 0, 2, 2, 2],
    [-4, 0, 0, 0, 0, 0, 0, 4],
    [-4, 0, 0, 0, 0, 0, 2, 2],
    [-3, -3, -1, -1, 1, 1, 3, 3],
    [-3, -3, -1, 1, 1, 1, 1, 3],
    [-3, -3, 1, 1, 1, 1, 1, 1],
    [-3, -1, -1, -1, -1, 1, 1, 5],
    [-3, -1, -1, -1, -1, 1, 3, 3],
    [-3, -1, -1, -1, 1, 1, 1, 3],
    [-3, -1, -1, 1, 1, 1, 1, 1],
    [-2, -2, -2, -2, 0, 2, 2, 4],
    [-2, -2, -2, -2, 2, 2, 2, 2],
    [-2, -2, -2, 0, 0, 0, 2, 4],
    [-2, -2, -2, 0, 0, 2, 2, 2],
    [-2, -2, 0, 0, 0, 0, 0, 4],
    [-2, -2, 0, 0, 0, 0, 2, 2],
    [-2, 0, 0, 0, 0, 0, 0, 2],
    [-1, -1, -1, -1, -1, -1, 1, 5],
    [-1, -1, -1, -1, -1, -1, 3, 3],
    [-1, -1, -1, -1, -1, 1, 1, 3],
    [-1, -1, -1, -1, 1, 1, 1, 1] ]

/-- Public name for the explicit divided component profiles used by the
structural E7 theory. -/
def e7MinedComponentProfiles : List (List ℤ) :=
  e7MinedNormProfileData

end SRG266
