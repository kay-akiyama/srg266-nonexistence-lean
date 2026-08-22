/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7MinedFrontierData

/-! # Root residual check for the mined E7 frontier -/

namespace SRG266

theorem e7MinedNormSubtree00 :
    e7MinedSubtree 4 ⟨8, 0, 0, [], []⟩ =
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
        [-4, -2, 0, 0, 0, 0, 2, 4] ] := by
  decide +kernel

end SRG266
