import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0151`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0151Mask : ℕ := 1039871336286448

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0151Witness : Array ℤ :=
  #[-83, -47, -11, -43, -1, 33, 33, -18, 3, 29, 13, -8, -10, 27, -49, -39,
  1, 0, 6, 13, -4, 60, 17, -2, 1, -30, 1, -16, -1, -72, -54, -36, 49, 20,
  -6, 64, 114, 37, -3, -6, -18, -19, 0, 33, -15, 52, -42, 71, -10, -68, 40,
  45, 4, -88, 35, 60, -30, 4, 43, -8, 64, -16, -29, -61, -27, -8, 36, -56,
  9, 5, -20, 15, -42, 69, -34, -15, -13, -7, 17, -54, 6, 10, 33, -19, 15,
  -12, 4, -2, -59, 48, -2, 34, 35, -16, -7, 34, -56, 7, 137, 9, 30, -30,
  -33, -39, -22, -25, 22, -163, 3, 25, 36, 38, -51, -78, 21, -59, 6, 26, 6,
  15, -21, 0, 58, 0, 23, -21, -37, -23, -20, -12, -59, -156, -96, -41, -3,
  158, -30, 65, 3, 13, 26, -64, 19, -3, 52, 7, 21, 28, -37, 6, 101, -38, 61,
  6, -67, 56, 15, -55, -47, 10, 58, -28, 26, 40, 15, 42, 101, -38]

theorem fractionalNearFrameSubtreeG1R0151_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0151Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0151Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0151Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0151_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0151LowerBoundTable : List ℤ :=
  [-52, 1, 23, -83, 3, 2, 2, 41, -25, 340, 19, -141, 70, -142, -67, 193, 10,
  87, 75, -18, -84, -46, -5, 10, 5]

def fractionalNearFrameSubtreeG1R0151LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0151Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0151LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
