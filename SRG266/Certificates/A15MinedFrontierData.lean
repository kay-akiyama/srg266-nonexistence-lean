/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedFrontier

/-!
# Three-level frontier data for the mined A15 search

The magnitude-six search reaches only 18 states after fixing magnitudes six,
five, and four. This shallow check does not evaluate any residual subtree.
-/

namespace SRG266

def a15MinedFrontier3 : List A15SmallMagState :=
  [ ⟨16, 0, 0, [], []⟩,
    ⟨15, 4, 16, [], [4]⟩,
    ⟨14, 8, 32, [], [4, 4]⟩,
    ⟨13, 12, 48, [], [4, 4, 4]⟩,
    ⟨15, -4, 16, [-4], []⟩,
    ⟨14, 0, 32, [-4], [4]⟩,
    ⟨13, 4, 48, [-4], [4, 4]⟩,
    ⟨14, -8, 32, [-4, -4], []⟩,
    ⟨13, -4, 48, [-4, -4], [4]⟩,
    ⟨13, -12, 48, [-4, -4, -4], []⟩,
    ⟨15, 5, 25, [], [5]⟩,
    ⟨14, 9, 41, [], [4, 5]⟩,
    ⟨14, 1, 41, [-4], [5]⟩,
    ⟨15, -5, 25, [-5], []⟩,
    ⟨14, -1, 41, [-5], [4]⟩,
    ⟨14, -9, 41, [-5, -4], []⟩,
    ⟨15, 6, 36, [], [6]⟩,
    ⟨15, -6, 36, [-6], []⟩ ]

theorem a15MinedFrontier3_checked :
    a15SmallFrontier 6 3 16 0 0 [] [] = a15MinedFrontier3 := by
  decide +kernel

end SRG266
