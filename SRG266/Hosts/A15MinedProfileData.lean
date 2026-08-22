/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15MinedNormProfileData
import SRG266.Hosts.A15MinedSearch

/-!
# Explicit profile data for the mined small A15 search

The definitions in this module are inert literals and the shell-threshold
filter applied to the 17 norm profiles. Evaluation certificates live in
separate bounded modules.
-/

namespace SRG266

/-- Filter the explicit complete norm list by the necessary shell bound. -/
def a15SmallCandidateProfiles : List (List ℤ) :=
  a15MinedNormProfiles.filter fun coordinates =>
    decide (74 ≤ a15SmallEligibleCount coordinates)

/-- Explicit normal form of the 15 profiles that pass the shell threshold. -/
def a15MinedCandidateProfiles : List (List ℤ) :=
  [a15MinedNormProfile00,
    a15MinedNormProfile02, a15MinedNormProfile03,
    a15MinedNormProfile04, a15MinedNormProfile05,
    a15MinedNormProfile06, a15MinedNormProfile07,
    a15MinedNormProfile08, a15MinedNormProfile09,
    a15MinedNormProfile11, a15MinedNormProfile12,
    a15MinedNormProfile13, a15MinedNormProfile14,
    a15MinedNormProfile15, a15MinedNormProfile16]

end SRG266
