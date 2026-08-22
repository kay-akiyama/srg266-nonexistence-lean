import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0236`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0236Mask : ℕ := 5091685559423249

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0236Witness : Array ℤ :=
  #[124, -24, 90, 25, -16, -58, -21, 75, -39, 87, 0, 4, 10, -36, -37, -22,
  -38, 10, 136, 13, -13, 12, 7, -80, -50, -36, 18, -19, 16, 32, -16, -12,
  -28, 60, -92, 0, 79, 43, -57, -9, -76, 32, -80, -9, -126, 139, 76, -28,
  -1, -39, 92, 49, -73, -29, 64, 43, 80, 54, -76, 1, -21, -26, -32, 78, 27,
  -57, -33, 51, 52, -5, -50, 26, 19, -10, 47, -8, 6, 36, -26, 34, -22, 8, 8,
  -23, 10, -16, -51, -36, -16, 10, 6, 41, -27, -12, 25, -17, 30, 29, -3, 7,
  24, -1, 32, 25, -49, 25, 27, -48, 0, -30, 26, -39, 19, 3, 9, -11, -20,
  -18, -27, 2, 42, 37, -5, -32, 34, 8, 9, 49, -10, 39, 44, -28, 17, -26, 8,
  -10, -41, 36, 78, 43, -4, -25, -20, -52, -16, 1, 30, 7, -9, -46, 18, 10,
  -72, -53, -15, 26, 6, 20, 20, 0, -3, -8, 54, -12, -19, 16, 77, 30]

theorem fractionalNearFrameSubtreeG2R0236_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0236Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0236Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0236Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0236_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0236LowerBoundTable : List ℤ :=
  [-3, -1, 69, -35, 2, 112, -124, 211, 196, 10, 44, 43, 48, 41, -78, 250,
  63, 41, 5, -6, -183, 61, 225, -162, 9]

def fractionalNearFrameSubtreeG2R0236LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0236Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0236LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
