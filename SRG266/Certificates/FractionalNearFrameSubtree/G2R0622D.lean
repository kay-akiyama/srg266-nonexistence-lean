import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0622`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0622Mask : ℕ := 9747980874139146

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0622Witness : Array ℤ :=
  #[-88, 65, 72, -72, -17, -86, 63, 114, 52, 163, 144, -114, -105, 81, -117,
  -40, 9, 51, 66, 14, -50, -72, -25, 18, -114, -8, 54, 47, 53, 55, 122, 13,
  40, -19, 133, -8, 53, 41, -24, -13, 75, 8, -6, 65, 19, -38, 78, -30, 39,
  70, 34, 77, -94, -48, 22, 105, 48, 24, -2, -122, 75, -9, 30, 66, 64, -173,
  -4, 41, 18, 5, -74, 82, 27, 100, 49, 6, -53, -11, 81, 86, -41, 27, 42, 32,
  -2, 0, 32, 132, -100, 3, -26, 119, -14, 33, -43, 108, -20, 41, -9, 41, 44,
  54, 94, -47, -2, -124, 32, -42, -41, -23, 47, 20, -72, -41, -68, 70, 20,
  34, 2, -35, -95, -79, -23, 53, -8, 106, 6, 93, -85, 17, -4, 135, -31, 13,
  14, -100, -44, 52, 91, -9, -61, 112, 119, -105, -7, 33, 20, -72, -142, 20,
  48, 68, -44, -46, -7, 85, -63, -6, 132, -13, -103, 130, 121, 48, -43, -11,
  0, 80]

theorem fractionalNearFrameSubtreeG2R0622_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0622Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0622Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0622Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0622_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0622LowerBoundTable : List ℤ :=
  [68, 80, 337, 24, 2, 130, 237, -30, 107, 9, 133, 8, 123, 201, 546, 9, 239,
  258, 31, 201, 42, 373, 122, 272, 656]

def fractionalNearFrameSubtreeG2R0622LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0622Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0622LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
