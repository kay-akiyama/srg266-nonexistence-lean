/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15MinedFrontierData

/-! # Bounded residual checks for mined A15 frontier states 0--5 -/

namespace SRG266

theorem a15MinedNormSubtree01 :
    a15SmallSubtree 3 ⟨15, 4, 16, [], [4]⟩ =
      [[-2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 4]] := by
  decide +kernel

theorem a15MinedNormSubtree02 :
    a15SmallSubtree 3 ⟨14, 8, 32, [], [4, 4]⟩ =
      [[-2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4]] := by
  decide +kernel

theorem a15MinedNormSubtree03 :
    a15SmallSubtree 3 ⟨13, 12, 48, [], [4, 4, 4]⟩ = [] := by
  decide +kernel

theorem a15MinedNormSubtree04 :
    a15SmallSubtree 3 ⟨15, -4, 16, [-4], []⟩ =
      [[-4, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2]] := by
  decide +kernel

theorem a15MinedNormSubtree05 :
    a15SmallSubtree 3 ⟨14, 0, 32, [-4], [4]⟩ =
      [[-4, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4]] := by
  decide +kernel

end SRG266
