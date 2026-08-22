/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7MinedFrontier

/-! # Two-level frontier data for the mined E7 norm search -/

namespace SRG266

def e7MinedFrontier2 : List E7MinedMagState :=
  [ ⟨8, 0, 0, [], []⟩,
    ⟨7, 5, 25, [], [5]⟩,
    ⟨7, -5, 25, [-5], []⟩,
    ⟨7, 6, 36, [], [6]⟩,
    ⟨7, -6, 36, [-6], []⟩ ]

theorem e7MinedFrontier2_checked :
    e7MinedFrontier 6 2 8 0 0 [] [] = e7MinedFrontier2 := by
  decide +kernel

end SRG266
