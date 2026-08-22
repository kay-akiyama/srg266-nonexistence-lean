import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0650`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0650Mask : ℕ := 36178237957329425

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0650Witness : Array ℤ :=
  #[-48, -7, -24, 7, 0, 309, 67, -10, 14, -3, -83, -92, 50, 2, 59, 7, 5, 40,
  -11, 8, 2, -2, 223, -21, 74, -21, -38, -39, 36, 13, 114, -225, -6, 18, 8,
  17, 178, -19, -8, 50, 33, 36, 1, 5, 105, -248, 0, -17, -75, -12, -12, 67,
  28, 19, 11, -5, 190, 7, 28, -35, -65, 19, 48, -24, 16, -11, 0, 138, -68,
  -30, 44, 4, 9, 6, -36, 166, 149, 23, -5, -46, 3, 13, 21, -4, -312, -5,
  -65, 27, -1, 52, 0, 11, -21, -58, 159, 20, -38, -27, -30, 49, 36, -109,
  -125, -139, -101, -36, -11, -15, -16, 7, 51, -11, 31, 273, -23, -40, -99,
  80, -66, -2, 68, -40, -69, 20, 23, -27, 8, 154, -10, -53, -43, -7, 24,
  -29, 167, -78, 16, 6, 9, -37, 164, 92, -37, 37, -9, 21, -32, 56, -3, 47,
  61, 36, 17, -82, 162, -7, -8, -306, -2, -9, -61, 119, -31, 123, -321, -58,
  111, -320]

theorem fractionalNearFrameSubtreeG2R0650_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0650Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0650Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0650Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0650_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0650LowerBoundTable : List ℤ :=
  [1, 3, 1, 2, 159, 207, 13, 1, 1, 249, 1, 17, 100, -240, 26, -13, 47, 129,
  231, -222, -8, -23, -72, 9, 161]

def fractionalNearFrameSubtreeG2R0650LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0650Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0650LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
