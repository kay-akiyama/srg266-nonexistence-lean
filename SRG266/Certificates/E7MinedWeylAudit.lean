/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedWeylChecksFirst
import SRG266.Certificates.E7MinedWeylChecksSecond
import SRG266.Certificates.E7MinedWeylCoverage

/-! # Assembly of the mined E7 Weyl compression -/

namespace SRG266

theorem e7MinedWeylCertificates_checked :
    e7MinedWeylCertificates.all E7MinedWeylCertificate.check = true := by
  rw [List.all_eq_true]
  intro certificate hcertificate
  simp only [e7MinedWeylCertificates, List.mem_cons, List.not_mem_nil,
    or_false] at hcertificate
  rcases hcertificate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact e7MinedWeylCertificate00_checked
  · exact e7MinedWeylCertificate01_checked
  · exact e7MinedWeylCertificate02_checked
  · exact e7MinedWeylCertificate03_checked
  · exact e7MinedWeylCertificate04_checked
  · exact e7MinedWeylCertificate05_checked
  · exact e7MinedWeylCertificate06_checked
  · exact e7MinedWeylCertificate07_checked
  · exact e7MinedWeylCertificate08_checked
  · exact e7MinedWeylCertificate09_checked
  · exact e7MinedWeylCertificate10_checked
  · exact e7MinedWeylCertificate11_checked
  · exact e7MinedWeylCertificate12_checked
  · exact e7MinedWeylCertificate13_checked
  · exact e7MinedWeylCertificate14_checked
  · exact e7MinedWeylCertificate15_checked
  · exact e7MinedWeylCertificate16_checked
  · exact e7MinedWeylCertificate17_checked
  · exact e7MinedWeylCertificate18_checked
  · exact e7MinedWeylCertificate19_checked
  · exact e7MinedWeylCertificate20_checked
  · exact e7MinedWeylCertificate21_checked
  · exact e7MinedWeylCertificate22_checked
  · exact e7MinedWeylCertificate23_checked
  · exact e7MinedWeylCertificate24_checked

/-- Every one of the 25 mined profiles carries a checked path to one of the
seven canonical component representatives. -/
theorem e7MinedProfile_hasWeylCertificate
    (coordinates : List ℤ)
    (hcoordinates : coordinates ∈ e7MinedComponentProfiles) :
    ∃ c ∈ e7MinedWeylCertificates,
      List.ofFn c.profile = coordinates ∧ c.Valid := by
  have hfin : coordinates ∈ e7MinedComponentProfiles.toFinset :=
    List.mem_toFinset.mpr hcoordinates
  rw [← e7MinedWeylSources_cover] at hfin
  have hsource : coordinates ∈ e7MinedWeylSourceProfiles :=
    List.mem_toFinset.mp hfin
  obtain ⟨c, hc, hprofile⟩ := List.mem_map.mp hsource
  refine ⟨c, hc, hprofile, ?_⟩
  exact c.valid_of_check
    ((List.all_eq_true.mp e7MinedWeylCertificates_checked) c hc)

end SRG266
