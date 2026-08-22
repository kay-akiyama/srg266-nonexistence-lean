import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0380`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0380Mask : ℕ := 5738160774095250

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0380Witness : Array ℤ :=
  #[-61, -22, -48, 46, -94, 37, -47, 9, -34, -51, -41, -7, 30, 43, 4, 61,
  -62, -38, -74, 78, -85, -14, 57, -12, 31, 0, 34, 30, 36, -41, 0, -29, -54,
  84, -51, 56, 7, 31, 28, 26, 45, 38, -79, 129, -4, 96, -49, -54, 23, -113,
  82, 19, 63, -82, -87, -12, -30, 22, -56, -89, 50, 107, -30, -21, 22, 66,
  78, -78, -8, -36, -43, 132, 24, 40, 65, 36, -17, -25, -4, 26, -155, -64,
  20, -64, 40, -25, 70, -47, 53, 90, 82, -27, 116, 67, -31, 78, 94, -55, -2,
  35, 42, -12, 8, -16, 112, -5, 54, -30, -1, 47, 21, 8, -16, -64, -37, -79,
  -51, -30, -6, -13, 73, -73, 69, -56, -102, -51, 42, -4, -7, -24, -42, -15,
  40, 79, 50, -48, 59, 5, -59, 17, 87, 4, 65, 34, 14, -91, 38, -62, 115, 17,
  75, -42, -7, -5, 5, -10, 21, 8, 19, -19, 43, -11, 3, -29, 24, -15, 4, -11]

theorem fractionalNearFrameSubtreeG2R0380_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0380Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0380Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0380Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0380_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0380LowerBoundTable : List ℤ :=
  [-42, 2, 90, 34, 168, 12, 70, 42, -149, 11, 175, 96, -41, 363, 137, 43,
  -317, 148, 9, 56, -51, 8, 12, 245, 256]

def fractionalNearFrameSubtreeG2R0380LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0380Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0380LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
