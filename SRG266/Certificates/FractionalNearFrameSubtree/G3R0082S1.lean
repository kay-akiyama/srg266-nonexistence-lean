import SRG266.Certificates.FractionalNearFrameSubtree.G3R0082S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G3R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0082_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0082Mask fractionalNearFrameSubtreeG3R0082Witness
      (fractionalNearFrameSubtreeG3R0082Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0082Mask (fractionalNearFrameSubtreeG3R0082Endpoint 0)).drop 48).take 12)
      (1066) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0082_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0082Mask fractionalNearFrameSubtreeG3R0082Witness
      (fractionalNearFrameSubtreeG3R0082Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0082Mask (fractionalNearFrameSubtreeG3R0082Endpoint 0)).drop 60).take 12)
      (1066) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0082_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0082Mask fractionalNearFrameSubtreeG3R0082Witness
      (fractionalNearFrameSubtreeG3R0082Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0082Mask (fractionalNearFrameSubtreeG3R0082Endpoint 0)).drop 72).take 12)
      (1066) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
