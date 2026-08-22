import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0465`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0465Mask : ℕ := 5807445017597202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0465Witness : Array ℤ :=
  #[-3, 233, 142, 142, 195, 159, -151, -135, -165, -247, -5, -70, 11, 53,
  99, -12, -157, 67, -17, -29, 54, 14, 21, 137, 0, 99, 30, 49, -72, 48,
  -195, -37, -111, 51, 11, 129, 196, 109, 19, -54, 119, 0, 145, 26, 69, -31,
  15, 82, 34, 82, 24, 46, 24, -36, -87, 30, -79, 64, -23, 79, 171, 42, -88,
  -106, -61, 94, -15, -3, 55, -41, 12, 15, 28, -85, -16, 63, -9, 44, 1, 87,
  -9, 37, 55, 55, -63, -44, 26, -68, 10, -40, 56, 2, 20, 21, -17, 96, 64,
  47, -2, -17, 91, -15, -35, 30, 62, -3, -50, -76, 96, -42, 64, 62, -2, 0,
  27, 42, 0, 138, -14, 0, -52, -74, 91, -48, -25, 29, 79, -65, 0, -188, -95,
  -3, 15, 62, -31, -109, 25, 45, 88, 92, 44, -17, 5, 68, 90, 40, -102, 98,
  23, -24, 88, -191, 17, -27, 41, -112, -21, 130, -88, 60, -34, 144, 19,
  -113, 95, 63, -68, -99]

theorem fractionalNearFrameSubtreeG2R0465_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0465Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0465Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0465Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0465_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0465LowerBoundTable : List ℤ :=
  [74, 37, 32, 3, 194, 374, 249, 205, -106, 306, 37, 10, -71, 10, 74, 185,
  -217, 9, 442, 134, 96, 430, 10, 650, 783]

def fractionalNearFrameSubtreeG2R0465LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0465Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0465LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
