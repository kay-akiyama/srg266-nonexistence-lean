import SRG266.Certificates.FractionalNearFrameSubtree.G3R0195D
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 0 for `G3R0195`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0195_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0195Mask fractionalNearFrameSubtreeG3R0195Witness
      (fractionalNearFrameSubtreeG3R0195Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0195Mask (fractionalNearFrameSubtreeG3R0195Endpoint 0)).drop 0).take 12)
      (-3894) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0195_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0195Mask fractionalNearFrameSubtreeG3R0195Witness
      (fractionalNearFrameSubtreeG3R0195Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0195Mask (fractionalNearFrameSubtreeG3R0195Endpoint 0)).drop 12).take 12)
      (-3894) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0195_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0195Mask fractionalNearFrameSubtreeG3R0195Witness
      (fractionalNearFrameSubtreeG3R0195Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0195Mask (fractionalNearFrameSubtreeG3R0195Endpoint 0)).drop 24).take 12)
      (-3894) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0195_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0195Mask fractionalNearFrameSubtreeG3R0195Witness
      (fractionalNearFrameSubtreeG3R0195Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0195Mask (fractionalNearFrameSubtreeG3R0195Endpoint 0)).drop 36).take 12)
      (-3894) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
