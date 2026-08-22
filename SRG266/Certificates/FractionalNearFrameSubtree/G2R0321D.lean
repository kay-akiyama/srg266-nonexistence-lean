import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0321`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0321Mask : ℕ := 5390065461749012

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0321Witness : Array ℤ :=
  #[0, -51, 164, 110, 66, 71, -17, 142, 125, 90, 41, -135, -154, -102, -46,
  -184, -65, -83, -21, -8, -90, -1, -11, -21, -53, -103, 78, 74, 69, -26,
  65, 21, -32, 101, 7, 19, -62, -22, 25, -44, -11, -9, -17, 43, -19, 2,
  -121, 23, 86, 67, 45, 100, 21, -23, -22, 93, 92, 44, -26, -136, 54, 23,
  -204, 60, 35, -153, -46, 72, -25, 59, -40, -6, 31, 42, 28, -3, 2, 100, -9,
  -21, 32, -120, 39, 3, 76, -39, 23, -49, -30, -66, 13, -39, -18, 45, 55,
  45, 65, 51, 38, -64, -8, 55, 1, -20, 41, 16, 53, 60, 43, 48, -38, -63,
  -42, -38, 54, -50, -3, 28, 16, 58, 24, 64, -78, -55, -25, 3, 13, -23, 42,
  25, 43, -3, -52, 33, 8, 40, -5, 52, 46, 21, 0, 113, 63, 0, 49, -85, 64,
  131, 71, -10, -118, -43, 6, 100, -7, -106, 49, -52, 41, 61, 39, 12, 32, 3,
  -19, 95, 84, -38]

theorem fractionalNearFrameSubtreeG2R0321_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0321Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0321Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0321Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0321_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0321LowerBoundTable : List ℤ :=
  [-17, 109, 147, -20, -63, -18, 18, 244, 6, -60, 240, 379, 165, 184, 150,
  248, 206, 10, -99, 365, 438, 9, 9, -106, 297]

def fractionalNearFrameSubtreeG2R0321LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0321Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0321LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
