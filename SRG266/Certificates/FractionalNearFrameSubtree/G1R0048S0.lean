import SRG266.Certificates.FractionalNearFrameSubtree.G1R0048D
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 0 for `G1R0048`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG1R0048_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0048Mask fractionalNearFrameSubtreeG1R0048Witness
      (fractionalNearFrameSubtreeG1R0048Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0048Mask (fractionalNearFrameSubtreeG1R0048Endpoint 0)).drop 0).take 12)
      (50) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0048_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0048Mask fractionalNearFrameSubtreeG1R0048Witness
      (fractionalNearFrameSubtreeG1R0048Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0048Mask (fractionalNearFrameSubtreeG1R0048Endpoint 0)).drop 12).take 12)
      (50) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0048_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0048Mask fractionalNearFrameSubtreeG1R0048Witness
      (fractionalNearFrameSubtreeG1R0048Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0048Mask (fractionalNearFrameSubtreeG1R0048Endpoint 0)).drop 24).take 12)
      (50) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG1R0048_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG1R0048Mask fractionalNearFrameSubtreeG1R0048Witness
      (fractionalNearFrameSubtreeG1R0048Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG1R0048Mask (fractionalNearFrameSubtreeG1R0048Endpoint 0)).drop 36).take 12)
      (50) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
