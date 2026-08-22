import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000Data
import SRG266.QuasiSymmetric.FractionalNearFrameSplitAudit

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Group 2 chunk 0000 tail theorem-mined Hall audit from local index 256

The exceptional weighted-Hall entry is isolated at local index 256.  The last
declaration proves the unbounded suffix, avoiding an external length claim.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0256_0257 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 256).take 1) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0257_0278 :
    FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 257) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0256 :
    FractionalNearFrameMinedEmptyRuleOn
      (fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 256) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_take_drop
  · exact fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0256_0257
  · simpa [List.drop_drop] using
      fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0257_0278

end SRG266.Certificates
