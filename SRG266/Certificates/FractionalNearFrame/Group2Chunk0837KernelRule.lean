import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837KernelHall0000
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837KernelHall0064
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837KernelHall0128
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837KernelHall0192
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837KernelHall0256
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Native-free group 2 chunk 0837 empty rule and masks
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2Chunk0837_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup2Chunk0837 := by
  have h192 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0837.drop 192) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0837_emptyShard0192
    · simpa [List.drop_drop] using
        fractionalNearFrameCertificatesGroup2Chunk0837_emptyShard0256
  have h128 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0837.drop 128) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0837_emptyShard0128
    · simpa [List.drop_drop] using h192
  have h64 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0837.drop 64) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0837_emptyShard0064
    · simpa [List.drop_drop] using h128
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · simpa using fractionalNearFrameCertificatesGroup2Chunk0837_emptyShard0000
  · exact h64

theorem fractionalNearFrameCertificatesGroup2Chunk0837_masks :
    fractionalNearFrameCertificatesGroup2Chunk0837.map
        FractionalNearFrameCertificateEntry.nearMask =
      (rootNearRepresentativeGroup2.drop 837).take 279 := by
  decide +kernel

end SRG266.Certificates
