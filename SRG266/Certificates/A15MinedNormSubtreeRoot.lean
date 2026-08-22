/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedFrontierData

/-! # Bounded residual check for the zero high-magnitude A15 state -/

namespace SRG266

theorem a15MinedNormSubtree00 :
    a15SmallSubtree 3 ⟨16, 0, 0, [], []⟩ =
      [ [-2, -2, -2, -2, -2, -2, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2],
        [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 3, 3, 3, 3],
        [-3, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 3, 3],
        [-3, -3, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 3, 3],
        [-3, -3, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3],
        [-3, -3, -3, -3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ] := by
  decide +kernel

end SRG266
