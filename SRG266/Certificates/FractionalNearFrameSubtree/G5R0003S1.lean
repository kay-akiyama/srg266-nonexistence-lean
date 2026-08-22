import SRG266.Certificates.FractionalNearFrameSubtree.G5R0003S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G5R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0003_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0003Mask fractionalNearFrameSubtreeG5R0003Witness
      (fractionalNearFrameSubtreeG5R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0003Mask (fractionalNearFrameSubtreeG5R0003Endpoint 0)).drop 48).take 12)
      (-119) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0003_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0003Mask fractionalNearFrameSubtreeG5R0003Witness
      (fractionalNearFrameSubtreeG5R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0003Mask (fractionalNearFrameSubtreeG5R0003Endpoint 0)).drop 60).take 12)
      (-119) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0003_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0003Mask fractionalNearFrameSubtreeG5R0003Witness
      (fractionalNearFrameSubtreeG5R0003Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0003Mask (fractionalNearFrameSubtreeG5R0003Endpoint 0)).drop 72).take 12)
      (-119) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
