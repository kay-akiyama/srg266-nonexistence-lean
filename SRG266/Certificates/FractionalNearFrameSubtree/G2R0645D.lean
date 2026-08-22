import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0645`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0645Mask : ℕ := 36107848997260297

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0645Witness : Array ℤ :=
  #[-138, -28, 0, -82, -111, -62, 36, 2, 33, 0, 118, 159, 12, -27, 26, -25,
  -20, -30, 31, -22, -11, -19, -35, -27, 11, -17, -28, 59, 22, 30, 37, -50,
  -7, 24, 34, -26, 26, -39, -30, 52, 26, 19, 18, 30, -34, 54, 26, -24, -38,
  -22, -2, -92, -8, 41, -51, 50, 16, 4, 27, 14, -45, -3, 0, -75, 86, 5, 44,
  0, 42, 0, -3, -13, 4, -94, -20, 2, 8, 5, -79, -12, 49, -77, 70, 38, 49,
  17, -23, 33, 36, 81, 93, -55, 58, 81, 29, 39, 64, 41, 48, 9, 66, 7, 4, 64,
  58, 62, 91, 9, 23, 107, 4, 29, 55, -17, 1, 81, -12, 89, -16, -30, -14, 75,
  72, 14, -32, -40, -2, -13, 119, -17, 19, 40, 16, 15, 79, -80, 16, 39, 28,
  -43, 49, -10, 21, -21, -82, -2, 20, 80, -67, -1, -11, 12, -46, 56, -45,
  -32, -2, 101, -16, 61, -32, 110, 0, -22, 47, -19, 48, 35]

theorem fractionalNearFrameSubtreeG2R0645_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0645Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0645Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0645Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0645_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0645LowerBoundTable : List ℤ :=
  [126, 353, 239, 78, 76, 243, -14, 2, -29, 452, 34, 85, -85, 62, 316, 63,
  303, -106, 154, -119, 179, 150, 45, 87, 365]

def fractionalNearFrameSubtreeG2R0645LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0645Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0645LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
