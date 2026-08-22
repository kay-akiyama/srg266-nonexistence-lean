import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0000
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0064
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0128
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0192
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0256
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0320
import SRG266.Certificates.FractionalNearFrame.Group5KernelHall0384
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Native-free group 5 empty rule and mask identification
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup5_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup5 := by
  have h320 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup5.drop 320) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup5_emptyShard0320
    · simpa [List.drop_drop] using
        fractionalNearFrameCertificatesGroup5_emptyShard0384
  have h256 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup5.drop 256) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup5_emptyShard0256
    · simpa [List.drop_drop] using h320
  have h192 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup5.drop 192) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup5_emptyShard0192
    · simpa [List.drop_drop] using h256
  have h128 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup5.drop 128) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup5_emptyShard0128
    · simpa [List.drop_drop] using h192
  have h64 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup5.drop 64) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup5_emptyShard0064
    · simpa [List.drop_drop] using h128
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · simpa using fractionalNearFrameCertificatesGroup5_emptyShard0000
  · exact h64

theorem fractionalNearFrameCertificatesGroup5_masks :
    fractionalNearFrameCertificatesGroup5.map
        FractionalNearFrameCertificateEntry.nearMask =
      rootNearRepresentativeGroup5 := by
  decide +kernel

end SRG266.Certificates
