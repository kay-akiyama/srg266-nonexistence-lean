import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0001Mask : ℕ := 260302672990723

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0001Witness : Array ℤ :=
  #[123, 139, 121, 212, -15, -9, -35, -117, -142, -219, -168, -182, 133,
  123, 127, 0, -67, -18, 14, -72, -87, 32, -118, -141, 152, 31, -32, 25,
  -33, 142, 76, 80, 121, -1, -50, -94, 8, -63, 18, 141, 63, 49, 73, 58, -4,
  -181, 107, -13, 97, 48, 68, 46, -49, 61, -7, -41, 6, -5, 30, -85, -4, 31,
  109, -2, 54, 23, 22, -98, -84, 10, -24, -39, 26, 47, -9, 7, 74, 54, -2,
  -5, -13, 37, -87, -109, 38, 4, -113, -38, -38, 171, -10, 28, 8, 7, 70, 60,
  -34, 31, 47, 42, 109, 44, -40, 50, -3, -23, 112, 78, -47, -62, 65, 11, 0,
  -27, -105, -17, 48, -55, -45, 45, -111, -2, -7, -3, 46, -4, -73, -52, -71,
  -22, 112, 49, -5, -35, 36, 137, 18, 152, 36, -5, -14, 40, 53, 88, 19, -73,
  69, 51, 2, 111, -33, 67, 103, 76, 59, -13, -45, -29, -50, 2, -40, -28,
  -64, -15, -30, -5, 81, 76]

theorem fractionalNearFrameSubtreeG3R0001_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0001Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0001Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0001Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0001_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0001LowerBoundTable : List ℤ :=
  [-6, 179, 2, 82, -47, 124, 129, 346, 168, -16, -26, 290, -52, 89, 322,
  116, 81, -60, 565, 182, 10, -319, 11, 135, 637]

def fractionalNearFrameSubtreeG3R0001LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0001Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0001LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
