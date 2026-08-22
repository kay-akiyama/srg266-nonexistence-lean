import SRG266.Certificates.FractionalNearFrameSubtree.G5R0016D
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 0 for `G5R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG5R0016_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0016Mask fractionalNearFrameSubtreeG5R0016Witness
      (fractionalNearFrameSubtreeG5R0016Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0016Mask (fractionalNearFrameSubtreeG5R0016Endpoint 0)).drop 0).take 12)
      (-145) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0016_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0016Mask fractionalNearFrameSubtreeG5R0016Witness
      (fractionalNearFrameSubtreeG5R0016Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0016Mask (fractionalNearFrameSubtreeG5R0016Endpoint 0)).drop 12).take 12)
      (-145) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0016_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0016Mask fractionalNearFrameSubtreeG5R0016Witness
      (fractionalNearFrameSubtreeG5R0016Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0016Mask (fractionalNearFrameSubtreeG5R0016Endpoint 0)).drop 24).take 12)
      (-145) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG5R0016_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG5R0016Mask fractionalNearFrameSubtreeG5R0016Witness
      (fractionalNearFrameSubtreeG5R0016Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG5R0016Mask (fractionalNearFrameSubtreeG5R0016Endpoint 0)).drop 36).take 12)
      (-145) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
