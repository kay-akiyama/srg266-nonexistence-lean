/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15MinedNormOutput
import SRG266.Hosts.A15MinedProfileData

/-!
# Certified mined A15 norm profiles

This module exposes only completeness of the 17-profile norm search.  The
independent eligible-cardinality filter belongs to `A15MinedProfile`, so
consumers that work directly with all norm profiles do not load its larger
reference-count proof.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- The norm-48 search evaluates to exactly 17 profiles. -/
theorem a15SmallNormProfiles_eq_mined_normOnly :
    a15SmallNormProfiles.toFinset = a15MinedNormProfiles.toFinset := by
  rw [a15SmallNormProfiles]
  rw [a15SmallEnumerateByMagnitudeAux_eq_frontier 3 3]
  rw [a15MinedFrontier3_checked, a15MinedNormSearchOutput_checked,
    a15MinedNormSearchOutput_toFinset]

/-- Completeness, stated against the explicit 17-profile normal form. -/
theorem a15SmallCanonicalCoordinates_mem_minedNormProfiles_normOnly
    (coordinates : List ℤ)
    (hlength : coordinates.length = 16)
    (hbounds : ∀ z ∈ coordinates, -6 ≤ z ∧ z ≤ 6)
    (hsum : coordinates.sum = 0)
    (hsq : (coordinates.map (fun z : ℤ => z * z)).sum = 48)
    (hparity :
      a15SmallCommonParity (a15SmallCanonicalCoordinates coordinates) = true) :
    a15SmallCanonicalCoordinates coordinates ∈ a15MinedNormProfiles := by
  have hmem := a15SmallCanonicalCoordinates_mem_normProfiles
    coordinates hlength hbounds hsum hsq hparity
  have hfin :
      a15SmallCanonicalCoordinates coordinates ∈ a15SmallNormProfiles.toFinset :=
    List.mem_toFinset.mpr hmem
  rw [a15SmallNormProfiles_eq_mined_normOnly] at hfin
  exact List.mem_toFinset.mp hfin

end SRG266
