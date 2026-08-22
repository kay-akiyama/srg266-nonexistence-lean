import SRG266.Certificates.FractionalNearFrameSubtree.G5R0072S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G5R0072`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0072_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0072Mask fractionalNearFrameSubtreeG5R0072Witness
      (fractionalNearFrameSubtreeG5R0072Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0072Mask (fractionalNearFrameSubtreeG5R0072Endpoint 0)).drop 48).take 12)
      (-16) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0072_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0072Mask fractionalNearFrameSubtreeG5R0072Witness
      (fractionalNearFrameSubtreeG5R0072Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0072Mask (fractionalNearFrameSubtreeG5R0072Endpoint 0)).drop 60).take 12)
      (-16) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0072_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0072Mask fractionalNearFrameSubtreeG5R0072Witness
      (fractionalNearFrameSubtreeG5R0072Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0072Mask (fractionalNearFrameSubtreeG5R0072Endpoint 0)).drop 72).take 12)
      (-16) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
