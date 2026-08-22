import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0546`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0546Mask : ℕ := 6834178655720012

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0546Witness : Array ℤ :=
  #[-76, -48, -76, -164, -93, 34, 23, 2, 28, 14, 37, 111, 90, 49, 38, 84,
  24, 86, -20, -29, -13, 81, 58, 27, 23, 77, -22, -95, -86, -43, 44, 37, 11,
  -50, 25, -4, 0, 26, -26, -5, 22, -63, 21, 46, 50, -74, -35, 10, 21, 58,
  78, -18, 1, -34, -114, 28, 21, 13, -9, -68, -53, -90, 35, 63, -22, 88,
  -45, 68, -74, 54, -34, 68, 70, -19, -78, -5, 27, -23, -57, -21, 4, 36, 46,
  12, 44, 34, 18, 19, 11, -51, 22, 93, -30, 106, 61, 36, -20, 34, 54, 96,
  63, 112, 55, -139, -62, 28, 22, -33, 57, -1, -8, 1, 13, -35, 25, -40, -62,
  22, -7, 6, 56, 29, 2, -84, -68, 104, 96, 0, 58, 25, 121, 24, 13, -57, 19,
  -24, -34, -3, 36, -36, -5, -18, -73, 8, 9, -23, 33, -39, 22, 36, 28, -12,
  -1, 18, 63, 84, -30, 4, -8, 28, 45, 1, -61, 28, -33, 54, 73, -68]

theorem fractionalNearFrameSubtreeG2R0546_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0546Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0546Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0546Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0546_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0546LowerBoundTable : List ℤ :=
  [19, 100, 32, 62, 59, 125, 3, 55, 113, -71, 77, 94, 4, 120, 225, 351, 170,
  271, 129, 9, 10, 70, 212, 212, 140]

def fractionalNearFrameSubtreeG2R0546LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0546Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0546LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
