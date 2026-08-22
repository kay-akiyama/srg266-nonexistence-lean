import SRG266.Certificates.FractionalNearFrameSubtree.G2R0364S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G2R0364`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0364_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0364Mask fractionalNearFrameSubtreeG2R0364Witness
      (fractionalNearFrameSubtreeG2R0364Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0364Mask (fractionalNearFrameSubtreeG2R0364Endpoint 0)).drop 48).take 12)
      (8) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0364_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0364Mask fractionalNearFrameSubtreeG2R0364Witness
      (fractionalNearFrameSubtreeG2R0364Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0364Mask (fractionalNearFrameSubtreeG2R0364Endpoint 0)).drop 60).take 12)
      (8) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0364_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0364Mask fractionalNearFrameSubtreeG2R0364Witness
      (fractionalNearFrameSubtreeG2R0364Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0364Mask (fractionalNearFrameSubtreeG2R0364Endpoint 0)).drop 72).take 12)
      (8) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
