import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0056`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0056Mask : ℕ := 4954180762049553

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0056Witness : Array ℤ :=
  #[-20, 4, -34, 3, -35, -35, 49, -24, -1, 5, 18, -8, 37, 9, 9, 40, 13, 16,
  15, -25, 12, -3, -8, 48, 25, 11, -52, -41, -25, -3, -12, 5, -18, 31, -2,
  14, -51, -11, -46, -5, 32, -11, 42, 11, -33, 17, -22, 57, 35, 22, 32, -11,
  -37, -29, 2, -32, 29, 6, 63, -45, -40, 0, -56, 3, -33, 13, -4, -62, 8, 76,
  67, 36, -23, -18, 17, -8, -13, -20, -11, 61, -36, -33, 9, -38, 11, 11, 7,
  -5, 12, -22, -49, 78, -15, 27, -19, 10, -29, -9, -11, 42, 3, 68, 42, -36,
  -25, 12, 6, 33, -2, -2, -10, 25, -17, -73, 48, 84, 47, 87, 34, 2, -106,
  -10, 35, 76, -8, -56, -51, -13, -46, -40, -87, -52, -30, -31, -5, 25, 4,
  26, -72, 18, -59, 33, 28, 4, -7, -15, 48, -12, 18, -25, 62, -1, -8, -43,
  2, 37, 31, -1, 16, 40, 70, 7, 10, -14, 31, 15, 32, -23]

theorem fractionalNearFrameSubtreeG5R0056_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0056Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0056Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0056Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0056_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0056LowerBoundTable : List ℤ :=
  [-40, 2, 2, 53, -5, 1, -32, 3, 2, 87, 134, -231, 50, 97, 188, 47, -129,
  93, 115, 149, 10, 9, 21, 54, -1]

def fractionalNearFrameSubtreeG5R0056LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0056Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0056LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
