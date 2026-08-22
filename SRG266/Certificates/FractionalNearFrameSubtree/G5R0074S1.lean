import SRG266.Certificates.FractionalNearFrameSubtree.G5R0074S0
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Empty-endpoint subtree shards 1 for `G5R0074`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0074_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0074Mask fractionalNearFrameSubtreeG5R0074Witness
      (fractionalNearFrameSubtreeG5R0074Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0074Mask (fractionalNearFrameSubtreeG5R0074Endpoint 0)).drop 48).take 12)
      (-12) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0074_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0074Mask fractionalNearFrameSubtreeG5R0074Witness
      (fractionalNearFrameSubtreeG5R0074Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0074Mask (fractionalNearFrameSubtreeG5R0074Endpoint 0)).drop 60).take 12)
      (-12) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0074_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0074Mask fractionalNearFrameSubtreeG5R0074Witness
      (fractionalNearFrameSubtreeG5R0074Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0074Mask (fractionalNearFrameSubtreeG5R0074Endpoint 0)).drop 72).take 12)
      (-12) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
