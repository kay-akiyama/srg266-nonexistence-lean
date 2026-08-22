import SRG266.Certificates.FractionalNearFrameSubtree.G2R0381S0
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 1 for `G2R0381`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0381_s0048 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0381Mask fractionalNearFrameSubtreeG2R0381Witness
      (fractionalNearFrameSubtreeG2R0381Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0381Mask (fractionalNearFrameSubtreeG2R0381Endpoint 0)).drop 48).take 12)
      (-38) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0381_s0060 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0381Mask fractionalNearFrameSubtreeG2R0381Witness
      (fractionalNearFrameSubtreeG2R0381Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0381Mask (fractionalNearFrameSubtreeG2R0381Endpoint 0)).drop 60).take 12)
      (-38) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0381_s0072 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0381Mask fractionalNearFrameSubtreeG2R0381Witness
      (fractionalNearFrameSubtreeG2R0381Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0381Mask (fractionalNearFrameSubtreeG2R0381Endpoint 0)).drop 72).take 12)
      (-38) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
