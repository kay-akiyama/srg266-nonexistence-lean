/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedFrontierData

/-! # Small residual checks for the mined E7 frontier -/

namespace SRG266

theorem e7MinedNormSubtree01 :
    e7MinedSubtree 4 ⟨7, 5, 25, [], [5]⟩ =
      [ [-1, -1, -1, -1, -1, -1, 1, 5],
        [-3, -1, -1, -1, -1, 1, 1, 5] ] := by
  decide +kernel

theorem e7MinedNormSubtree02 :
    e7MinedSubtree 4 ⟨7, -5, 25, [-5], []⟩ =
      [ [-5, -1, 1, 1, 1, 1, 1, 1],
        [-5, -1, -1, 1, 1, 1, 1, 3] ] := by
  decide +kernel

theorem e7MinedNormSubtree03 :
    e7MinedSubtree 4 ⟨7, 6, 36, [], [6]⟩ = [] := by
  decide +kernel

theorem e7MinedNormSubtree04 :
    e7MinedSubtree 4 ⟨7, -6, 36, [-6], []⟩ = [] := by
  decide +kernel

end SRG266
