import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0182`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0182Mask : ℕ := 6866159493124770

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0182Witness : Array ℤ :=
  #[41, -26, 18, 46, 0, 10, -65, -100, 17, -35, -2, 33, -49, 61, -58, 64,
  -17, -67, 24, -63, -50, 16, -24, -55, 40, -15, 46, -26, 96, 40, 66, 129,
  47, 17, -34, -48, -37, 92, -18, 52, -51, -33, 4, -87, -124, 0, 64, 25,
  101, 48, 113, 23, 119, 18, 33, 69, -48, 53, -37, -31, -74, 67, 94, -24,
  34, -142, 67, 109, 13, 122, -22, 126, 16, -135, 75, 16, 1, 96, 36, -26,
  -15, 31, -32, -68, 76, -35, -28, -9, 25, -53, -64, -21, -41, 104, 24, 99,
  32, -30, -106, 37, 88, 93, 69, 73, 85, 42, 13, -33, 94, 55, 105, -37, 37,
  187, 138, 165, -89, 168, -46, 72, 17, 24, 85, 21, 131, 0, -33, 34, 70, 4,
  58, -36, 221, 25, 28, -138, -42, -45, -24, 29, 149, 41, 10, 35, 42, 36,
  41, 142, 135, 120, 20, -89, 27, 60, -99, -119, 55, 74, 56, -60, 126, -39,
  -7, -84, -9, 12, -77, -27]

theorem fractionalNearFrameSubtreeG3R0182_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0182Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0182Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0182Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0182_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0182LowerBoundTable : List ℤ :=
  [156, 358, 158, 227, 170, 130, 2, 181, 308, 423, -118, 345, 760, 377, 233,
  339, 553, 33, 19, 298, 366, 308, 9, 240, 206]

def fractionalNearFrameSubtreeG3R0182LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0182Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0182LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
