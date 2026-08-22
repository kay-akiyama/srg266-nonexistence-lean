import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0001`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0001Mask : ℕ := 521910773260419

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0001Witness : Array ℤ :=
  #[100, -3, -12, -2, -38, -11, 97, 14, 11, -16, -2, -29, 0, -35, -66, -53,
  77, -21, -75, 35, -39, -15, -13, -48, -22, -79, -38, 66, 17, -1, 35, 0,
  76, 92, 70, 51, 29, 33, -96, -45, 11, 8, -55, -10, -41, -74, -51, 5, 3,
  -20, 56, -37, -2, -64, -48, -71, 53, -45, -33, -6, 5, -7, 7, 75, -19, 34,
  -24, 5, -19, -50, 10, 25, 87, 0, 39, 117, 59, -10, -36, -16, 30, -20, -42,
  -9, 58, -115, -66, 51, 26, -53, 45, 6, 33, 28, -26, 49, 48, -17, -12, -34,
  54, 53, -82, 30, -14, 28, 13, -84, -58, -96, -68, 18, -7, 20, 7, 38, 42,
  21, 13, 32, 3, 53, 27, -54, -14, -33, -60, -55, -78, 42, -43, -23, -10,
  55, 29, 18, 55, -84, -53, -1, 18, -21, -1, -10, 77, -61, 4, 63, 33, -76,
  34, -28, 28, 3, -24, -6, -27, 32, -24, -45, -25, 115, 51, 99, 5, 71, 53,
  56]

theorem fractionalNearFrameSubtreeG5R0001_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0001Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0001Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0001Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0001_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0001LowerBoundTable : List ℤ :=
  [-54, 18, 87, -44, 2, -60, 1, 2, 2, -57, 24, 55, -56, 215, 309, 132, -21,
  6, -177, -81, -129, 38, 111, 10, 22]

def fractionalNearFrameSubtreeG5R0001LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0001Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0001LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
