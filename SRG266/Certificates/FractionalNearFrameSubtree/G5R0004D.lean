import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0004`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0004Mask : ℕ := 546898358272067

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0004Witness : Array ℤ :=
  #[46, 16, 126, -137, -14, -71, -69, 0, 28, -111, -18, 6, 33, 38, -17, -59,
  -81, -77, 7, -69, -23, -83, 91, 16, -37, -13, -12, 64, 0, 23, 8, 80, -34,
  -38, -103, -30, -46, -66, -80, 57, 73, -15, 25, -20, -11, -21, 0, -2, 26,
  74, -73, -34, 55, 74, -20, -12, -34, 34, 56, 48, 20, 130, -25, -12, 22,
  -23, -35, 91, 33, 105, -67, -13, -16, -30, 44, -67, -62, 165, 43, -53, 54,
  66, -12, 42, 23, 66, 85, 39, 84, 16, 42, -79, 13, -13, -58, 32, 34, 103,
  120, 23, -51, 115, -30, 69, -18, 13, 8, 0, 86, -230, -197, -128, -144, 81,
  34, 69, -86, -34, -25, -122, -94, -36, -1, -107, -46, 4, -26, -18, -31,
  -53, -66, -126, 14, 65, -161, -120, 26, 224, -20, 113, -82, -8, 107, 97,
  -3, 82, 24, 57, 61, 117, 55, -34, 38, -1, -93, -55, -27, -48, -71, -112,
  -55, 19, 22, 0, 31, -53, 76, 16]

theorem fractionalNearFrameSubtreeG5R0004_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0004Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0004Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0004Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0004_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0004LowerBoundTable : List ℤ :=
  [-161, -76, -13, -19, 51, -30, 39, -28, 2, 38, -66, 10, -138, 131, -42,
  -264, 23, 12, 10, -71, -231, 252, -30, 90, 53]

def fractionalNearFrameSubtreeG5R0004LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0004Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0004LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
