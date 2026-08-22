import SRG266.Certificates.FractionalNearFrameSubtree.G1R0113S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G1R0113`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0113_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0113Mask fractionalNearFrameSubtreeG1R0113Witness
      (fractionalNearFrameSubtreeG1R0113Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0113Mask (fractionalNearFrameSubtreeG1R0113Endpoint 0)).drop 48).take 12)
      (32) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0113_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0113Mask fractionalNearFrameSubtreeG1R0113Witness
      (fractionalNearFrameSubtreeG1R0113Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0113Mask (fractionalNearFrameSubtreeG1R0113Endpoint 0)).drop 60).take 12)
      (32) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0113_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0113Mask fractionalNearFrameSubtreeG1R0113Witness
      (fractionalNearFrameSubtreeG1R0113Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0113Mask (fractionalNearFrameSubtreeG1R0113Endpoint 0)).drop 72).take 12)
      (32) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
