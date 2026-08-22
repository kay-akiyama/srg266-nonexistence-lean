import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0110`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0110Mask : ℕ := 5792746721675779

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0110Witness : Array ℤ :=
  #[56, 38, 50, 57, -3, -63, -81, -83, -14, -25, -88, 76, 79, -8, 112, 66,
  -80, 43, 2, 76, 5, 16, -11, 64, 53, 51, 14, -19, -24, 0, -74, -13, -6, -7,
  -11, -65, 85, -8, 8, 0, 3, 35, 37, 51, 18, 98, 77, 70, 57, 38, 32, 3,
  -144, -57, 39, 29, -66, -46, -85, 31, -5, 47, -36, -48, -9, -59, -13, -19,
  37, 22, -35, -74, 21, 6, -8, 13, 38, -104, -47, -142, 47, 126, -20, 8,
  -50, -65, -87, 46, -12, -89, 4, -3, 92, 35, 22, -46, 25, 0, 18, 43, 28,
  24, -31, -19, 53, 0, 43, -62, -19, 37, -48, 91, 132, 133, 21, 27, -19, 9,
  44, -22, -1, -12, 20, -5, 52, 6, 47, 4, -53, 35, 22, 47, 125, -32, 47,
  -53, 0, -133, 54, -75, 59, -74, 57, -52, -72, 10, -1, 25, 49, 28, 28, 29,
  -23, 15, -73, -40, -23, -3, 13, 14, 93, -23, 29, -41, -35, -7, -94, 46]

theorem fractionalNearFrameSubtreeG5R0110_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0110Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0110Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0110Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0110_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0110LowerBoundTable : List ℤ :=
  [-7, 31, -41, 36, 122, 25, 77, 2, 53, 273, 73, -14, 10, 37, 9, 100, 10,
  231, 125, 174, -267, 86, 172, 153, 10]

def fractionalNearFrameSubtreeG5R0110LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0110Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0110LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
