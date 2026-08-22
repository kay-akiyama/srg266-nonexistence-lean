import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000Data
import SRG266.QuasiSymmetric.FractionalNearFrameSplitAudit

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Group 2 chunk 0000 tail theorem-mined Hall audit from local index 0

Bounded kernel declarations for the payload-free Hall stratum.  Farkas entries
are ignored here and checked by the residual audit in the chunk aggregator.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0000_0008 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 0).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0008_0016 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 8).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0016_0024 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 16).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0024_0032 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 24).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0032_0040 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 32).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0040_0048 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 40).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0048_0056 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 48).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0056_0064 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 56).take 8) := by
  apply fractionalNearFrameMinedEmptyRuleOn_of_audit
  decide +kernel

theorem fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyShard0000 :
    FractionalNearFrameMinedEmptyRuleOn
      ((fractionalNearFrameCertificatesGroup2Chunk0000Tail.drop 0).take 64) := by
  have h16 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 8 8
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0000_0008
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0008_0016
  have h24 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 16 8 h16
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0016_0024
  have h32 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 24 8 h24
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0024_0032
  have h40 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 32 8 h32
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0032_0040
  have h48 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 40 8 h40
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0040_0048
  have h56 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 48 8 h48
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0048_0056
  have h64 := fractionalNearFrameMinedEmptyRuleOn_of_adjacent_ranges
    fractionalNearFrameCertificatesGroup2Chunk0000Tail 0 56 8 h56
    fractionalNearFrameCertificatesGroup2Chunk0000Tail_empty_0056_0064
  exact h64

end SRG266.Certificates
