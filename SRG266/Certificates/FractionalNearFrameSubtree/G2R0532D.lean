import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0532`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0532Mask : ℕ := 6794661768141841

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0532Witness : Array ℤ :=
  #[-99, -48, -6, 40, 22, 72, -82, -44, -45, -50, 0, 79, -81, 4, 31, -12, 1,
  52, 137, 22, 13, 61, 19, -63, -59, -40, -37, -35, 18, 73, -17, 49, -119,
  -19, 27, 78, 47, -26, -24, 21, -141, -58, -85, -22, 57, 8, -48, -2, 80,
  26, -8, 2, -17, -29, -9, 4, 121, 52, -1, 13, 10, 23, -13, 41, 20, -14, 9,
  57, 31, -79, 27, 93, 7, 16, -1, -10, 30, 43, 0, 18, -50, -44, -15, 61, -1,
  2, 7, 13, -21, -1, 28, 22, 11, 19, 17, -9, 3, 26, -4, 43, 1, 2, -38, 87,
  100, 68, 9, -44, 38, 37, 5, 19, 4, 47, -25, 9, -54, -47, -31, 10, -38, 11,
  -43, 3, 55, 46, 62, 49, 0, 18, -70, -115, 38, 0, 44, 24, 34, 9, -27, -26,
  -18, 7, 0, 48, 3, 22, 14, -18, -42, 43, 61, 16, -20, -84, -52, -21, 75,
  36, -21, -15, 19, 38, 33, -21, -17, 7, 17, 45]

theorem fractionalNearFrameSubtreeG2R0532_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0532Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0532Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0532Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0532_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0532LowerBoundTable : List ℤ :=
  [8, 2, 138, 145, 102, 120, 51, 2, -50, 60, 73, 94, 97, -5, 68, 245, 17,
  -161, -46, -29, 301, 184, -49, 49, 5]

def fractionalNearFrameSubtreeG2R0532LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0532Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0532LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
