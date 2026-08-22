import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0267`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0267Mask : ℕ := 5369778201565848

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0267Witness : Array ℤ :=
  #[-41, 24, -19, -25, 10, 30, 33, 47, 25, 35, -8, -38, -20, 0, -67, -5, 35,
  -29, -4, 6, -4, 33, 19, 12, -5, 7, 46, 32, -14, -36, -46, 24, 40, -30,
  -17, 36, 40, 62, 14, -16, 40, 50, -21, 21, 22, -12, -32, -72, 32, 30, 18,
  -10, -10, -23, 0, 43, -27, 9, -31, -12, 27, 21, -5, 28, -41, -45, -8, 11,
  52, -1, -4, 47, -4, -3, -59, 16, -32, 18, 33, -42, -36, 68, 51, -48, -32,
  71, -35, -39, -3, -3, 45, 9, 29, 49, -25, 19, 30, -51, 10, 9, -8, 34, 23,
  24, -5, 17, 22, -3, 20, -62, 3, 2, -52, 38, 0, 56, 22, 15, 13, 3, -10,
  -26, 30, 56, 33, -59, -15, -50, -6, 2, 53, 61, -46, -38, -23, 29, -6, -4,
  -43, 5, -35, -13, -14, 4, -59, -43, -27, 66, 26, 25, 66, 19, 29, 14, -9,
  28, 34, -37, -50, -1, 7, -22, -1, 4, -18, 50, 70, -55]

theorem fractionalNearFrameSubtreeG2R0267_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0267Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0267Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0267Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0267_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0267LowerBoundTable : List ℤ :=
  [-9, 34, 64, 58, 44, 1, 3, 2, 62, 151, -50, -92, -1, 99, 178, 44, 87, 128,
  111, 10, 9, -49, 59, 123, 101]

def fractionalNearFrameSubtreeG2R0267LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0267Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0267LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
