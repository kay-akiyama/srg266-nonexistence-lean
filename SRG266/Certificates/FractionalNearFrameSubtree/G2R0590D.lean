import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0590`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0590Mask : ℕ := 6863938252416274

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0590Witness : Array ℤ :=
  #[-15, -12, 3, 29, 17, -22, -76, -18, -95, -64, -45, 77, 73, 46, 39, 39,
  -44, -45, -17, -20, -26, -7, 28, 59, -12, 0, -11, -14, 85, -9, -209, -32,
  -17, 58, 17, 36, 19, 50, 15, -31, -47, 47, 8, 17, -174, -5, -27, 39, 34,
  -1, 1, -22, 35, 15, -6, 90, -105, -67, -139, 90, 88, 75, 142, 31, -11, 11,
  78, 68, 78, 119, 40, 17, -5, 7, -69, -9, 2, 22, 16, 14, -63, 30, -26, -31,
  -2, 42, 55, 0, 26, -103, -4, 1, 50, -59, 6, 121, 16, -20, -10, 29, -10, 4,
  34, -27, -11, 145, 11, -53, -40, -63, 3, 0, -40, 48, 25, 0, 27, 77, -16,
  0, 47, -22, -25, -44, -82, -75, 25, 11, -86, 12, 29, -13, -36, -51, -23,
  -58, -19, 37, 56, -15, -7, 166, 16, 7, 16, 5, -5, 8, 90, 62, -17, -8, 171,
  1, 23, -134, -47, -67, 61, -118, 6, -59, 23, 21, -50, 19, -127, -34]

theorem fractionalNearFrameSubtreeG2R0590_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0590Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0590Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0590Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0590_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0590LowerBoundTable : List ℤ :=
  [-26, -75, -18, 149, -76, 67, 54, 2, 2, 62, 70, 185, 131, 10, -30, 24,
  -142, -63, 225, -157, 141, 10, -29, 88, 80]

def fractionalNearFrameSubtreeG2R0590LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0590Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0590LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
