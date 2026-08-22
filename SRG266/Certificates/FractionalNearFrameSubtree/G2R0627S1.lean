import SRG266.Certificates.FractionalNearFrameSubtree.G2R0627S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G2R0627`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0627_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0627Mask fractionalNearFrameSubtreeG2R0627Witness
      (fractionalNearFrameSubtreeG2R0627Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0627Mask (fractionalNearFrameSubtreeG2R0627Endpoint 0)).drop 48).take 12)
      (61) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0627_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0627Mask fractionalNearFrameSubtreeG2R0627Witness
      (fractionalNearFrameSubtreeG2R0627Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0627Mask (fractionalNearFrameSubtreeG2R0627Endpoint 0)).drop 60).take 12)
      (61) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0627_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0627Mask fractionalNearFrameSubtreeG2R0627Witness
      (fractionalNearFrameSubtreeG2R0627Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0627Mask (fractionalNearFrameSubtreeG2R0627Endpoint 0)).drop 72).take 12)
      (61) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
