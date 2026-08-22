import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0122`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0122Mask : ℕ := 5402280448430296

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0122Witness : Array ℤ :=
  #[73, 71, -9, 36, -43, 61, -4, 80, 84, 66, -71, 9, -81, -99, -21, -13, 72,
  -37, 16, -92, 24, 7, 128, 5, 82, -32, 66, 43, 100, 52, -12, -69, -18,
  -111, 115, 102, -65, 4, -116, -110, 130, 90, 105, 121, -62, -6, -85, 28,
  2, 69, -76, -7, -39, 23, 148, 100, 66, -64, -45, 24, -47, -51, 3, -45,
  -30, 11, 67, -26, -29, -121, -13, 11, 75, -73, 11, -50, 87, 9, 32, 2, -19,
  -12, 75, -81, 14, -49, 10, 6, -27, 9, -11, 2, -66, 39, -7, 25, 13, -85,
  43, 130, 49, 13, 124, 92, 45, 65, 20, -12, 26, 58, 99, -10, -14, -46, -17,
  -2, 18, -28, -2, 130, 76, 38, -96, -54, -109, -55, -17, -8, -38, -6, 73,
  -2, -83, 65, -92, -62, -42, -29, -55, -10, 29, 81, -88, -65, -100, 65, 38,
  26, -4, -74, -34, 15, 43, 208, -38, -47, 82, 141, -123, -24, 63, 43, 59,
  47, 35, 100, 0, -28]

theorem fractionalNearFrameSubtreeG3R0122_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0122Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0122Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0122Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0122_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0122LowerBoundTable : List ℤ :=
  [-4, 1, 290, 67, 2, -23, 39, 71, 177, 9, 212, 138, 36, 347, 159, -29, 507,
  -30, 240, 93, 38, 83, -133, 10, 269]

def fractionalNearFrameSubtreeG3R0122LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0122Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0122LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
