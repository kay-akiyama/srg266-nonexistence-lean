import SRG266.Certificates.FractionalNearFrameSubtree.G5R0059S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G5R0059`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0059_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0059Mask fractionalNearFrameSubtreeG5R0059Witness
      (fractionalNearFrameSubtreeG5R0059Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0059Mask (fractionalNearFrameSubtreeG5R0059Endpoint 0)).drop 48).take 12)
      (-330) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0059_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0059Mask fractionalNearFrameSubtreeG5R0059Witness
      (fractionalNearFrameSubtreeG5R0059Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0059Mask (fractionalNearFrameSubtreeG5R0059Endpoint 0)).drop 60).take 12)
      (-330) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0059_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0059Mask fractionalNearFrameSubtreeG5R0059Witness
      (fractionalNearFrameSubtreeG5R0059Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0059Mask (fractionalNearFrameSubtreeG5R0059Endpoint 0)).drop 72).take 12)
      (-330) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
