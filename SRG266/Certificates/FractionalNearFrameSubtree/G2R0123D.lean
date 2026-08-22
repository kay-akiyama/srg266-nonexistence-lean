import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0123`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0123Mask : ℕ := 1323105077679121

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0123Witness : Array ℤ :=
  #[-87, -89, -60, 41, -79, -81, 2, 47, 18, 89, 0, 68, -19, -26, 24, 26, 38,
  15, -25, -43, -87, -37, -84, 15, -15, -30, -17, 6, 35, 37, 72, 82, -46,
  -50, 64, -44, -35, 59, 18, 41, -54, -35, -7, -25, 25, 52, -33, 14, 4, 23,
  9, 19, 8, -6, -71, 50, -10, 11, -3, 56, -6, -28, -12, 59, 29, -19, 34, 20,
  -16, 4, 8, 34, 23, -99, 76, -3, -62, -78, -68, -91, 38, 56, -36, -13, -40,
  12, 3, -28, 58, 23, 44, -39, 27, 68, -9, -12, -1, 4, 24, -17, -2, -74, 42,
  72, 12, -35, 31, -25, 33, 18, -20, -9, -8, 43, 26, 32, 33, 13, 10, 0, 37,
  -32, 8, 3, 0, -13, 87, 23, -80, 21, 2, 10, 46, -27, 44, 27, 18, -1, 25,
  38, -14, -54, -12, 8, 17, -22, 62, 25, -32, 48, -6, -12, 81, -54, 30, -14,
  -51, 0, -20, 27, -6, 5, -11, 5, 12, 6, -30, -5]

theorem fractionalNearFrameSubtreeG2R0123_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0123Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0123Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0123Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0123_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0123LowerBoundTable : List ℤ :=
  [-12, 58, 20, 2, 2, 20, 58, 2, 2, 269, -50, 135, -64, -122, 101, -25, 106,
  -25, -57, -9, 11, 164, -3, 9, 70]

def fractionalNearFrameSubtreeG2R0123LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0123Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0123LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
