/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7MinedWeylData

/-! # Bounded checks for mined E7 Weyl certificates 0--12 -/

namespace SRG266

theorem e7MinedWeylCertificate00_checked :
    (e7MinedWeylCertificates.get ⟨0, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate01_checked :
    (e7MinedWeylCertificates.get ⟨1, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate02_checked :
    (e7MinedWeylCertificates.get ⟨2, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate03_checked :
    (e7MinedWeylCertificates.get ⟨3, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate04_checked :
    (e7MinedWeylCertificates.get ⟨4, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate05_checked :
    (e7MinedWeylCertificates.get ⟨5, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate06_checked :
    (e7MinedWeylCertificates.get ⟨6, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate07_checked :
    (e7MinedWeylCertificates.get ⟨7, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate08_checked :
    (e7MinedWeylCertificates.get ⟨8, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate09_checked :
    (e7MinedWeylCertificates.get ⟨9, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate10_checked :
    (e7MinedWeylCertificates.get ⟨10, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate11_checked :
    (e7MinedWeylCertificates.get ⟨11, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate12_checked :
    (e7MinedWeylCertificates.get ⟨12, by decide⟩).check = true := by
  decide +kernel

end SRG266
