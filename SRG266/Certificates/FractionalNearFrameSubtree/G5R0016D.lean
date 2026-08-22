import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0016Mask : ℕ := 1015451974602833

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0016Witness : Array ℤ :=
  #[-48, -80, 13, 51, -76, -43, 64, 40, -6, 12, 22, -2, -54, -40, -59, -17,
  7, -63, -35, 61, -51, 22, 20, 48, 6, -5, 48, -67, -22, -32, 10, 7, 17, 8,
  -16, 43, 51, -46, -46, -54, 0, -15, -53, -14, -72, 4, 13, 0, 30, 75, -2,
  -85, 0, 76, -7, -81, -59, 17, 66, 47, -9, -19, 33, -102, -79, 45, 34, -36,
  0, 32, -27, 45, -6, -4, -34, -56, -75, 5, 44, 17, -63, 10, -95, -11, 49,
  33, -36, 2, -68, 5, 20, -12, -74, 89, -20, -11, 26, -59, -42, 18, -18,
  -13, 35, 52, -20, 15, 46, -6, -59, -116, 12, -36, -23, -11, 19, -86, 12,
  -17, -64, -97, 33, 6, -52, -77, -28, -3, 42, 83, 30, 32, 0, -24, 19, -3,
  20, 84, -103, -108, 74, 11, -58, -2, 12, 12, -18, 46, 1, 0, 24, 28, 5, -4,
  0, -54, -86, 99, 29, -4, -8, -26, 91, -15, -38, 45, 57, 59, 88, 38]

theorem fractionalNearFrameSubtreeG5R0016_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0016Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0016Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0016Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0016_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0016LowerBoundTable : List ℤ :=
  [-145, 12, -27, -1, -152, -58, -39, -75, -174, 247, -297, -88, 14, 264,
  -48, 9, -148, 28, 228, -35, -265, -233, -60, 56, 58]

def fractionalNearFrameSubtreeG5R0016LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0016Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0016LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
