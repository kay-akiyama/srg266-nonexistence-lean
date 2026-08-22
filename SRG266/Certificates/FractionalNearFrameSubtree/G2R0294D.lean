import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0294`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0294Mask : ℕ := 5386217173263634

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0294Witness : Array ℤ :=
  #[-65, -30, 58, -7, 17, -35, 46, 92, 90, 136, 72, -107, 0, -126, -65, 33,
  -115, 10, 38, 44, -120, -67, 23, 5, -28, 5, 45, 49, 111, 38, 1, -76, -54,
  -48, -18, 131, -31, 42, 12, 25, -33, 29, 119, 78, 17, 2, 38, 35, 70, -98,
  -9, 25, 16, -2, 33, -106, 44, -26, -15, 0, 69, 56, -53, -9, 83, -55, -54,
  -53, -72, 16, 32, 43, -28, -43, 74, -21, 17, -55, -8, -87, 8, -38, 55,
  -99, 106, 18, 49, 26, 4, 56, 28, 77, -84, 20, -18, 35, -40, 60, -22, 26,
  -8, 113, 85, 0, -23, 17, 107, -21, 50, 60, 65, -121, 12, 16, 117, -79, 5,
  29, -63, -15, 52, -113, 23, -4, -62, -48, 16, -87, -22, 69, 59, 62, 118,
  -27, 57, 7, 45, -77, 24, 142, -43, 52, 128, -5, 63, -76, -54, 58, 43, 35,
  -60, -41, -21, 56, -9, -134, -69, 117, -15, -38, -22, 33, -35, -10, -35,
  15, -82, -6]

theorem fractionalNearFrameSubtreeG2R0294_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0294Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0294Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0294Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0294_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0294LowerBoundTable : List ℤ :=
  [8, 2, 28, 119, 2, 170, 1, 131, 3, -88, 254, 493, 23, 119, -186, 73, -18,
  67, 11, 246, 199, 312, -203, 56, 144]

def fractionalNearFrameSubtreeG2R0294LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0294Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0294LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
