import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0087`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0087Mask : ℕ := 936547459140172

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0087Witness : Array ℤ :=
  #[33, 106, -72, -153, -37, 67, -13, -50, -3, 91, 19, 155, 67, 11, 12, -50,
  0, 67, 38, -8, 1, 83, -14, 56, 3, 0, 37, -11, -29, -129, -159, -31, 33,
  -14, -50, -25, 44, 144, 209, -72, -74, 146, -32, 75, -175, 72, 134, -21,
  96, -13, -12, 102, 180, -166, -78, -159, -40, 38, -24, 126, 45, -21, -26,
  24, 54, 40, 76, 17, -51, 44, 48, 87, -44, 31, 25, -61, 56, 24, -6, 197,
  160, 164, 41, 50, -19, 48, -27, -42, 68, 128, 81, 136, 85, 77, 75, 217,
  175, 73, -37, 21, 93, -15, 27, 35, 108, 103, 45, 87, 41, -28, 96, 36, 4,
  27, -93, -32, -6, -118, -15, 10, 17, 65, 72, 96, 70, -71, 64, -49, -4,
  -58, -46, -38, 45, 114, 93, 23, -219, 40, -6, 120, -25, 65, 19, -103, -45,
  -59, -58, -22, 5, -75, 30, 193, -2, -82, -35, 22, 123, 173, -18, -63, 182,
  79, -56, -122, -177, -9, 40, 144]

theorem fractionalNearFrameSubtreeG1R0087_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0087Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0087Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0087Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0087_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0087LowerBoundTable : List ℤ :=
  [156, 2, 310, 472, 406, 253, 201, 2, 189, 262, 29, 28, 246, 636, 17, 152,
  87, 1086, 35, 488, 285, 464, 72, 571, 44]

def fractionalNearFrameSubtreeG1R0087LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0087Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0087LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
