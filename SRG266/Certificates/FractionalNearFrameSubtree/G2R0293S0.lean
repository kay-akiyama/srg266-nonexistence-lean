import SRG266.Certificates.FractionalNearFrameSubtree.G2R0293D
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Empty-endpoint subtree shards 0 for `G2R0293`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

theorem fractionalNearFrameSubtreeG2R0293_s0000 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0293Mask fractionalNearFrameSubtreeG2R0293Witness
      (fractionalNearFrameSubtreeG2R0293Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0293Mask (fractionalNearFrameSubtreeG2R0293Endpoint 0)).drop 0).take 12)
      (-102) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0293_s0012 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0293Mask fractionalNearFrameSubtreeG2R0293Witness
      (fractionalNearFrameSubtreeG2R0293Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0293Mask (fractionalNearFrameSubtreeG2R0293Endpoint 0)).drop 12).take 12)
      (-102) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0293_s0024 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0293Mask fractionalNearFrameSubtreeG2R0293Witness
      (fractionalNearFrameSubtreeG2R0293Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0293Mask (fractionalNearFrameSubtreeG2R0293Endpoint 0)).drop 24).take 12)
      (-102) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

theorem fractionalNearFrameSubtreeG2R0293_s0036 :
    CompactShellSubtreeLowerBoundOn fractionalNearFrameSubtreeG2R0293Mask fractionalNearFrameSubtreeG2R0293Witness
      (fractionalNearFrameSubtreeG2R0293Endpoint 0)
      (((compactShellRootChildren fractionalNearFrameSubtreeG2R0293Mask (fractionalNearFrameSubtreeG2R0293Endpoint 0)).drop 36).take 12)
      (-102) := by
  apply compactShellSubtreeLowerBoundOn_of_audit
  decide +kernel

end SRG266.Certificates
