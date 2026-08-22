import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0168`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0168Mask : ℕ := 1380465457406308

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0168Witness : Array ℤ :=
  #[47, 60, 0, -131, -78, 27, 141, -54, -35, -9, -57, 93, 191, 49, 56, 117,
  14, -3, -64, -76, -177, 14, 127, -61, 43, 35, 51, 44, -14, 62, 54, -12,
  -149, -65, -71, 113, 76, -68, -126, -4, -90, 55, 3, 57, -25, -80, 67, -14,
  44, -36, -47, 0, -8, -23, 76, 35, -9, -24, 111, -42, -22, -176, 53, 53,
  30, -4, -56, 20, 36, 147, 85, 266, 19, 156, -54, -38, 73, -63, 132, -40,
  -176, 28, 59, -49, 94, -7, 120, 13, 5, 183, 27, -113, 45, 41, 116, 117,
  116, 125, 270, 127, 162, -97, -35, 7, -17, 1, 89, 65, -20, 7, 39, 41, -8,
  66, 21, -98, 79, -126, 17, -76, -54, -38, 29, 114, 11, 128, 202, -177, 52,
  44, -41, 87, 63, -24, -4, -42, 31, -18, 102, 15, -22, 68, 39, 66, 56, 68,
  38, 152, 72, 16, -28, -66, -31, 58, -56, -68, -177, -118, -7, 161, -40,
  -13, -28, 57, -52, 2, 13, -46]

theorem fractionalNearFrameSubtreeG2R0168_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0168Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0168Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0168Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0168_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0168LowerBoundTable : List ℤ :=
  [58, 81, 284, 428, 244, 2, 122, 2, 337, 170, 22, 146, 320, 418, 146, 9,
  251, 433, 200, -55, 548, 578, 395, -123, 118]

def fractionalNearFrameSubtreeG2R0168LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0168Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0168LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
