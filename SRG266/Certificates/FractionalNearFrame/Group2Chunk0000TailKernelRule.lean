import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailHall0000
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailHall0064
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailHall0128
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailHall0192
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailHall0256
import SRG266.Certificates.RootNearRepresentatives

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Native-free group 2 chunk 0000 tail empty rule and masks
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyRule :
    FractionalNearFrameMinedEmptyRuleOn
      fractionalNearFrameCertificatesGroup2Chunk0000Tail := by
  have h192 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 192) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0192
    · simpa [List.drop_drop] using
        fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0256
  have h128 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 128) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0128
    · simpa [List.drop_drop] using h192
  have h64 : FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 64) := by
    apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
    · exact fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0064
    · simpa [List.drop_drop] using h128
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · simpa using fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0000
  · exact h64

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_masks :
    fractionalNearFrameCertificatesGroup2Chunk0000Tail.map
        FractionalNearFrameCertificateEntry.nearMask =
      (rootNearRepresentativeGroup2.drop 1).take 278 := by
  decide +kernel

end SRG266.Certificates
