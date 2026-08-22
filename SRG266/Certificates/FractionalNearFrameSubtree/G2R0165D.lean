import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0165`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0165Mask : ℕ := 1380190596284756

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0165Witness : Array ℤ :=
  #[-139, 0, -106, -90, -65, 42, 28, -8, -6, -41, 30, -1, 108, 87, 65, 49,
  -7, 54, 19, -67, -61, 67, 42, 94, 37, -72, 64, 42, 22, 0, -24, -56, 67,
  -19, -77, 216, 107, -52, -75, -187, -128, 77, 148, 86, 110, 212, 127, 3,
  18, -135, -119, -33, 7, -53, 18, -22, -72, -111, 15, 109, -104, 96, 17,
  27, -132, -8, 110, -60, -29, 55, -22, -108, -3, 45, -14, 24, -27, 44, -10,
  38, 16, -53, 53, -164, -53, 18, -15, -84, 60, 97, -115, -59, 17, 101, -22,
  4, 95, -50, 69, -73, -28, 53, 38, -134, 87, 13, -41, 13, -19, 71, 12, 74,
  8, 7, -13, -79, -80, 14, -54, 82, 27, -30, -45, 50, 9, -27, -90, -93, 90,
  24, 20, -62, -66, 47, 32, -13, 9, 64, 178, -192, 7, 79, -54, 90, 101, -7,
  35, 70, 18, 22, 100, 67, -44, 85, 0, -33, -77, -63, 33, -139, 118, -11,
  -27, -29, 26, -41, 48, 1]

theorem fractionalNearFrameSubtreeG2R0165_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0165Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0165Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0165Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0165_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0165LowerBoundTable : List ℤ :=
  [-70, 61, 29, -100, -7, -7, 1, 105, -15, 19, 115, 229, 127, 176, -214, 11,
  33, 10, 171, 82, 276, 150, 84, 4, 321]

def fractionalNearFrameSubtreeG2R0165LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0165Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0165LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
