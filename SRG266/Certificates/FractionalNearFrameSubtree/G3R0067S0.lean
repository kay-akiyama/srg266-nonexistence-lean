import SRG266.Certificates.FractionalNearFrameSubtree.G3R0067D
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 0 for `G3R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG3R0067_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0067Mask fractionalNearFrameSubtreeG3R0067Witness
      (fractionalNearFrameSubtreeG3R0067Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0067Mask (fractionalNearFrameSubtreeG3R0067Endpoint 0)).drop 0).take 12)
      (-81) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0067_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0067Mask fractionalNearFrameSubtreeG3R0067Witness
      (fractionalNearFrameSubtreeG3R0067Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0067Mask (fractionalNearFrameSubtreeG3R0067Endpoint 0)).drop 12).take 12)
      (-81) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0067_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0067Mask fractionalNearFrameSubtreeG3R0067Witness
      (fractionalNearFrameSubtreeG3R0067Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0067Mask (fractionalNearFrameSubtreeG3R0067Endpoint 0)).drop 24).take 12)
      (-81) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG3R0067_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG3R0067Mask fractionalNearFrameSubtreeG3R0067Witness
      (fractionalNearFrameSubtreeG3R0067Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG3R0067Mask (fractionalNearFrameSubtreeG3R0067Endpoint 0)).drop 36).take 12)
      (-81) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
