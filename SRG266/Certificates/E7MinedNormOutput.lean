/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedNormSubtreeRoot
import SRG266.Certificates.E7MinedNormSubtrees
import SRG266.Hosts.E7MinedProfileData
import Mathlib.Data.Finset.Dedup

/-! # Assembly of the bounded mined E7 norm output -/

namespace SRG266

def e7MinedNormSearchOutput : List (List ℤ) :=
  [ [-1, -1, -1, -1, 1, 1, 1, 1],
    [-2, 0, 0, 0, 0, 0, 0, 2],
    [-2, -2, 0, 0, 0, 0, 2, 2],
    [-2, -2, -2, 0, 0, 2, 2, 2],
    [-2, -2, -2, -2, 2, 2, 2, 2],
    [-1, -1, -1, -1, -1, 1, 1, 3],
    [-1, -1, -1, -1, -1, -1, 3, 3],
    [-3, -1, -1, 1, 1, 1, 1, 1],
    [-3, -1, -1, -1, 1, 1, 1, 3],
    [-3, -1, -1, -1, -1, 1, 3, 3],
    [-3, -3, 1, 1, 1, 1, 1, 1],
    [-3, -3, -1, 1, 1, 1, 1, 3],
    [-3, -3, -1, -1, 1, 1, 3, 3],
    [-2, -2, 0, 0, 0, 0, 0, 4],
    [-2, -2, -2, 0, 0, 0, 2, 4],
    [-2, -2, -2, -2, 0, 2, 2, 4],
    [-4, 0, 0, 0, 0, 0, 2, 2],
    [-4, -2, 0, 0, 0, 2, 2, 2],
    [-4, -2, -2, 0, 2, 2, 2, 2],
    [-4, 0, 0, 0, 0, 0, 0, 4],
    [-4, -2, 0, 0, 0, 0, 2, 4],
    [-1, -1, -1, -1, -1, -1, 1, 5],
    [-3, -1, -1, -1, -1, 1, 1, 5],
    [-5, -1, 1, 1, 1, 1, 1, 1],
    [-5, -1, -1, 1, 1, 1, 1, 3] ]

theorem e7MinedNormSearchOutput_checked :
    e7MinedExpand 4 e7MinedFrontier2 = e7MinedNormSearchOutput := by
  simp only [e7MinedExpand, e7MinedFrontier2,
    List.flatMap_cons, List.flatMap_nil,
    List.append_nil,
    e7MinedNormSubtree00, e7MinedNormSubtree01,
    e7MinedNormSubtree02, e7MinedNormSubtree03,
    e7MinedNormSubtree04, e7MinedNormSearchOutput]
  rfl

theorem e7MinedNormSearchOutput_toFinset :
    e7MinedNormSearchOutput.toFinset = e7MinedNormProfileData.toFinset := by
  decide +kernel

end SRG266
