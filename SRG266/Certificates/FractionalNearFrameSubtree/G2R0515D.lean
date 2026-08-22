import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0515`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0515Mask : ℕ := 5812724874774896

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0515Witness : Array ℤ :=
  #[154, 7, 58, 17, 80, 30, -102, 19, -40, 76, -9, -55, -53, -16, 30, -136,
  -35, -75, -46, -10, 47, -71, 61, -65, 80, 53, 53, 146, -56, 95, 19, 59, 0,
  169, -135, -94, -58, 123, 62, 215, -53, -242, -115, -31, -61, -178, 17,
  113, 167, 129, -43, 18, -84, 44, 131, 124, 0, -42, 31, 68, 37, 61, -42,
  95, 49, -38, 30, -55, -30, -40, 43, 8, 38, -34, 22, 71, -58, 66, 20, 7,
  -34, -14, -67, 24, 8, -60, -44, 21, 24, -5, 15, -25, -16, -8, -69, 37, 79,
  44, -24, 1, -15, 9, -3, 51, 23, -21, 23, 17, 82, -21, 143, 64, 58, -61,
  -31, 40, 75, 34, -54, -6, -25, 59, 2, 64, -22, 16, -52, 145, 61, 28, -14,
  101, 62, 0, -10, -22, -108, -60, -57, 85, -2, -31, 35, -36, -49, 17, -1,
  133, -41, -103, -105, -139, -16, 34, 68, 132, 74, -94, 44, 14, 20, 136,
  23, 74, -36, -27, -66, -6]

theorem fractionalNearFrameSubtreeG2R0515_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0515Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0515Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0515Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0515_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0515LowerBoundTable : List ℤ :=
  [24, 44, 141, 2, 64, 159, 319, 3, 66, 10, 396, 347, 8, 111, 367, 186, 77,
  106, -66, 74, -8, 66, -33, 422, 9]

def fractionalNearFrameSubtreeG2R0515LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0515Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0515LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
