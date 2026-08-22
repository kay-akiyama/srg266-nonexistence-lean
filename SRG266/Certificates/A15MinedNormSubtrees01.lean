/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedFrontierData

/-! # Bounded residual checks for mined A15 frontier states 6--11 -/

namespace SRG266

theorem a15MinedNormSubtree06 :
    a15SmallSubtree 3 ⟨13, 4, 48, [-4], [4, 4]⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree07 :
    a15SmallSubtree 3 ⟨14, -8, 32, [-4, -4], []⟩ =
      [[-4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2]] := by
  decide +kernel

theorem a15MinedNormSubtree08 :
    a15SmallSubtree 3 ⟨13, -4, 48, [-4, -4], [4]⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree09 :
    a15SmallSubtree 3 ⟨13, -12, 48, [-4, -4, -4], []⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree10 :
    a15SmallSubtree 3 ⟨15, 5, 25, [], [5]⟩ =
      [ [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 5],
        [-3, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 5] ] := by
  decide +kernel

theorem a15MinedNormSubtree11 :
    a15SmallSubtree 3 ⟨14, 9, 41, [], [4, 5]⟩ = [] := by
  decide +kernel

end SRG266
