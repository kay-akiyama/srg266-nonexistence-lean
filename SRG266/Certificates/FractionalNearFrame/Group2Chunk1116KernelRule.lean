import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116KernelHall0000
import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116KernelHall0064
import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116KernelHall0128
import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116KernelHall0192
import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116KernelHall0256
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Native-free group 2 chunk 1116 empty rule and masks
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2Chunk1116_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup2Chunk1116 := by
  have h192 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk1116.drop 192) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk1116_emptyShard0192
    · simpa [List.drop_drop] using
        fractionalNearFrameCertificatesGroup2Chunk1116_emptyShard0256
  have h128 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk1116.drop 128) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk1116_emptyShard0128
    · simpa [List.drop_drop] using h192
  have h64 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk1116.drop 64) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk1116_emptyShard0064
    · simpa [List.drop_drop] using h128
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · simpa using fractionalNearFrameCertificatesGroup2Chunk1116_emptyShard0000
  · exact h64

theorem fractionalNearFrameCertificatesGroup2Chunk1116_masks :
    fractionalNearFrameCertificatesGroup2Chunk1116.map
        FractionalNearFrameCertificateEntry.nearMask =
      (rootNearRepresentativeGroup2.drop 1116).take 279 := by
  decide +kernel

end SRG266.Certificates
