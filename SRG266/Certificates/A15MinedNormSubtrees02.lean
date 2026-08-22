/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedFrontierData

/-! # Bounded residual checks for mined A15 frontier states 12--17 -/

namespace SRG266

theorem a15MinedNormSubtree12 :
    a15SmallSubtree 3 ⟨14, 1, 41, [-4], [5]⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree13 :
    a15SmallSubtree 3 ⟨15, -5, 25, [-5], []⟩ =
      [ [-5, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 3],
        [-5, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ] := by
  decide +kernel

theorem a15MinedNormSubtree14 :
    a15SmallSubtree 3 ⟨14, -1, 41, [-5], [4]⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree15 :
    a15SmallSubtree 3 ⟨14, -9, 41, [-5, -4], []⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree16 :
    a15SmallSubtree 3 ⟨15, 6, 36, [], [6]⟩ =
      [[-2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6]] := by
  decide +kernel

theorem a15MinedNormSubtree17 :
    a15SmallSubtree 3 ⟨15, -6, 36, [-6], []⟩ =
      [[-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2]] := by
  decide +kernel

end SRG266
