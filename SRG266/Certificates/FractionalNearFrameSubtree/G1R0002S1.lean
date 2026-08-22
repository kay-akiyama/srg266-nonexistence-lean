import SRG266.Certificates.FractionalNearFrameSubtree.G1R0002S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G1R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0002_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0002Mask fractionalNearFrameSubtreeG1R0002Witness
      (fractionalNearFrameSubtreeG1R0002Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0002Mask (fractionalNearFrameSubtreeG1R0002Endpoint 0)).drop 48).take 12)
      (-133) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0002_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0002Mask fractionalNearFrameSubtreeG1R0002Witness
      (fractionalNearFrameSubtreeG1R0002Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0002Mask (fractionalNearFrameSubtreeG1R0002Endpoint 0)).drop 60).take 12)
      (-133) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0002_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0002Mask fractionalNearFrameSubtreeG1R0002Witness
      (fractionalNearFrameSubtreeG1R0002Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0002Mask (fractionalNearFrameSubtreeG1R0002Endpoint 0)).drop 72).take 12)
      (-133) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
