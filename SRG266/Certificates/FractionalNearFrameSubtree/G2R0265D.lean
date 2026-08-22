import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0265`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0265Mask : ℕ := 5369590010992140

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0265Witness : Array ℤ :=
  #[125, 87, 24, 65, 180, 50, 23, 31, -1, 32, 34, -77, -121, -117, 199, 0,
  42, 45, 45, 16, 222, -180, -166, -166, 219, -65, 77, -18, 190, 79, 82,
  -79, -32, -11, 89, 15, 154, -140, -43, -20, 105, 64, 53, -19, -76, 229,
  -5, -230, -44, -41, 64, 74, 46, 0, 128, 1, -41, -31, -72, 84, 58, -61, 93,
  -67, -54, -91, 7, -22, -19, 8, 0, 72, 73, 23, -42, -10, -50, -6, -3, 26,
  66, 52, -95, 343, 144, 9, 82, -44, 12, 110, -1, 211, 66, 13, 103, -224,
  30, -11, 14, -150, -101, 1, 113, 263, 43, 64, 61, 120, 208, -57, -214,
  -27, 194, 33, 135, -51, 108, 190, 113, 153, 192, -45, 37, 168, 95, -16,
  -63, -38, 157, -100, 29, 137, 232, -151, 138, -1, -40, 24, 13, -83, 62,
  140, 98, 19, 82, -10, 102, 61, 44, -48, 66, 84, 160, -54, -38, 65, 14,
  -78, 185, 92, 49, 165, 80, -32, 42, -114, -342, 93]

theorem fractionalNearFrameSubtreeG2R0265_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0265Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0265Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0265Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0265_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0265LowerBoundTable : List ℤ :=
  [306, 475, 138, 342, 174, 221, 462, 417, 234, 508, 670, 777, 592, -154,
  157, 631, 662, 437, 458, 608, 279, -7, 341, 325, 230]

def fractionalNearFrameSubtreeG2R0265LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0265Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0265LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
