import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0000
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0064
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0128
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0192
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0256
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0320
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0384
import SRG266.Certificates.FractionalNearFrame.Group3KernelHall0448
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Native-free group 3 empty rule and mask identification
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup3_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup3 := by
  have h384 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 384) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0384
    · simpa [List.drop_drop] using
        fractionalNearFrameCertificatesGroup3_emptyShard0448
  have h320 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 320) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0320
    · simpa [List.drop_drop] using h384
  have h256 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 256) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0256
    · simpa [List.drop_drop] using h320
  have h192 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 192) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0192
    · simpa [List.drop_drop] using h256
  have h128 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 128) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0128
    · simpa [List.drop_drop] using h192
  have h64 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup3.drop 64) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup3_emptyShard0064
    · simpa [List.drop_drop] using h128
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · simpa using fractionalNearFrameCertificatesGroup3_emptyShard0000
  · exact h64

theorem fractionalNearFrameCertificatesGroup3_masks :
    fractionalNearFrameCertificatesGroup3.map
        FractionalNearFrameCertificateEntry.nearMask =
      rootNearRepresentativeGroup3 := by
  decide +kernel

end SRG266.Certificates
