import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0097`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0097Mask : ℕ := 5541763877667154

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0097Witness : Array ℤ :=
  #[16, -24, -86, -103, 7, 0, 0, 41, 63, 153, 98, 90, 35, -68, -93, -20, -4,
  10, -65, 44, -75, 12, 76, 7, 80, 72, 58, -24, -40, 2, 87, 13, -25, 38,
  -16, 48, -68, -105, 70, 47, -48, -272, 30, 0, 70, 63, 73, 30, 52, -99,
  -90, -50, 34, 21, -113, -27, 76, 46, 84, -91, 71, 94, -25, 44, 83, 60,
  -47, 109, 62, -7, 55, 4, 59, -33, -33, 4, 27, -2, 20, 24, -43, 29, 103,
  -89, 56, 33, 71, -100, 83, 72, 43, -44, -12, 74, 32, -28, -29, -30, -3,
  -28, -56, 29, -36, -29, -84, -106, -1, 94, -1, 65, 27, -47, -31, 18, -37,
  -32, -76, 16, 121, 16, 20, 47, 40, -83, -71, 20, 38, 11, 52, -3, 21, 1,
  -27, 28, -45, 10, 9, 49, 22, 65, 38, -18, -86, 70, 73, -30, 31, 89, 4,
  -25, 104, -28, -63, 61, 57, -188, 23, 25, 111, -18, -13, 51, 14, 30, 38,
  58, 5, 40]

theorem fractionalNearFrameSubtreeG5R0097_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0097Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0097Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0097Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0097_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0097LowerBoundTable : List ℤ :=
  [20, 148, 2, 1, 191, 2, 2, 118, 260, -59, 195, 59, 178, 182, 455, 202,
  305, 336, 10, 106, 11, 9, -205, 156, 267]

def fractionalNearFrameSubtreeG5R0097LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0097Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0097LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
