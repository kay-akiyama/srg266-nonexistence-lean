import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0120`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0120Mask : ℕ := 5827654117728353

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0120Witness : Array ℤ :=
  #[88, 19, 28, 35, 67, 44, -55, -24, -49, -23, -37, -54, -38, -60, 5, 0, 8,
  40, -39, 15, 12, -19, 21, -4, 28, 61, -96, -63, -80, 36, -14, 16, -24, 13,
  -26, -36, 21, 52, -27, 16, 1, 41, 24, -40, -18, 13, 6, -5, 0, 115, 28, 20,
  0, 0, -57, -84, -103, 32, -12, -17, 13, 121, 62, -10, 6, -32, -49, -37,
  -25, 21, -46, 8, 66, 16, -7, -27, 23, 14, -8, 9, -31, -62, 33, -31, 6, 86,
  -5, 19, -14, -54, 19, 4, -21, -16, -14, 120, 42, -17, 0, 23, -44, -54, 37,
  -77, -14, 14, -30, -89, -123, 16, 72, 135, 3, 12, 30, -46, -19, -13, 51,
  11, -56, 12, 48, 10, 73, -70, 41, 12, 43, -7, -7, -19, -25, 30, 27, -56,
  -35, -23, 11, -3, -9, -48, 63, -42, -3, 15, 5, 23, 31, 76, -74, 9, 43, 17,
  24, -48, 40, -22, 57, 75, 9, 62, 15, 28, -5, 50, -95, 7]

theorem fractionalNearFrameSubtreeG5R0120_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0120Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0120Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0120Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0120_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0120LowerBoundTable : List ℤ :=
  [-56, 63, 11, 2, 3, 66, -40, -18, 2, 167, 58, -106, 10, -229, 248, 9, 137,
  -67, 85, 162, 76, 8, 10, 169, -50]

def fractionalNearFrameSubtreeG5R0120LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0120Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0120LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
