/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7MinedWeylData

/-! # Bounded checks for mined E7 Weyl certificates 13--24 -/

namespace SRG266

theorem e7MinedWeylCertificate13_checked :
    (e7MinedWeylCertificates.get ⟨13, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate14_checked :
    (e7MinedWeylCertificates.get ⟨14, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate15_checked :
    (e7MinedWeylCertificates.get ⟨15, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate16_checked :
    (e7MinedWeylCertificates.get ⟨16, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate17_checked :
    (e7MinedWeylCertificates.get ⟨17, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate18_checked :
    (e7MinedWeylCertificates.get ⟨18, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate19_checked :
    (e7MinedWeylCertificates.get ⟨19, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate20_checked :
    (e7MinedWeylCertificates.get ⟨20, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate21_checked :
    (e7MinedWeylCertificates.get ⟨21, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate22_checked :
    (e7MinedWeylCertificates.get ⟨22, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate23_checked :
    (e7MinedWeylCertificates.get ⟨23, by decide⟩).check = true := by
  decide +kernel

theorem e7MinedWeylCertificate24_checked :
    (e7MinedWeylCertificates.get ⟨24, by decide⟩).check = true := by
  decide +kernel

end SRG266
