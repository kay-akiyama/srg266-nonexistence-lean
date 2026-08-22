/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedNormSubtreeRoot
import SRG266.Certificates.A15MinedNormSubtrees00
import SRG266.Certificates.A15MinedNormSubtrees01
import SRG266.Certificates.A15MinedNormSubtrees02
import SRG266.Hosts.A15MinedNormProfileData
import Mathlib.Data.Finset.Dedup

/-!
# Assembly of the bounded mined A15 norm output

The three-level frontier exposes 18 residual subtrees. Their independent
checks are assembled by rewriting only; the complete recursion is never
evaluated in this module.
-/

namespace SRG266

/-- Search-order output of the 18 checked residual subtrees. -/
def a15MinedNormSearchOutput : List (List ℤ) :=
  [ [-2, -2, -2, -2, -2, -2, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2],
    [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 3, 3, 3, 3],
    [-3, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 3, 3],
    [-3, -3, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 3, 3],
    [-3, -3, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3],
    [-3, -3, -3, -3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [-2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 4],
    [-2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4],
    [-4, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2],
    [-4, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4],
    [-4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2],
    [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 5],
    [-3, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 5],
    [-5, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 3],
    [-5, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [-2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6],
    [-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2] ]

theorem a15MinedNormSearchOutput_checked :
    a15SmallExpand 3 a15MinedFrontier3 = a15MinedNormSearchOutput := by
  simp only [a15SmallExpand, a15MinedFrontier3,
    List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.append_nil,
    a15MinedNormSubtree00, a15MinedNormSubtree01,
    a15MinedNormSubtree02, a15MinedNormSubtree03,
    a15MinedNormSubtree04, a15MinedNormSubtree05,
    a15MinedNormSubtree06, a15MinedNormSubtree07,
    a15MinedNormSubtree08, a15MinedNormSubtree09,
    a15MinedNormSubtree10, a15MinedNormSubtree11,
    a15MinedNormSubtree12, a15MinedNormSubtree13,
    a15MinedNormSubtree14, a15MinedNormSubtree15,
    a15MinedNormSubtree16, a15MinedNormSubtree17,
    a15MinedNormSearchOutput]
  rfl

/-- The search-order literal and the canonical literal have the same set. -/
theorem a15MinedNormSearchOutput_toFinset :
    a15MinedNormSearchOutput.toFinset = a15MinedNormProfiles.toFinset := by
  decide +kernel

end SRG266
