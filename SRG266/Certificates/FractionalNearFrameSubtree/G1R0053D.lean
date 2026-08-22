import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0053`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0053Mask : ℕ := 682616073865489

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0053Witness : Array ℤ :=
  #[126, 120, 187, 210, 213, 212, 181, 114, 194, 201, 62, 144, -361, -269,
  -348, -350, -188, -297, 85, -202, -190, -38, -43, 63, -206, -54, -204,
  -74, 222, 310, 233, 345, 41, 68, 67, 97, -81, -43, -32, -4, -14, 15, -19,
  -41, -118, 29, 29, 8, -10, 9, 2, 2, -28, -8, -18, -43, 19, 12, 51, -16,
  -6, 26, 20, -90, -9, 31, 16, 26, -53, -32, -2, 20, -12, 0, -16, -25, 9,
  -10, 3, 31, 7, 5, 28, -37, 3, -57, 0, -46, 30, -24, -3, 10, -43, -24, 13,
  69, -2, 12, 13, -1, 37, 3, 11, -8, -32, -51, 36, 23, 44, 53, 10, -3, -7,
  -6, 35, -32, -41, -134, -24, -16, -32, 28, 24, -49, 16, -64, 12, -12, -13,
  -22, -36, 38, 9, -28, 1, 28, -47, -51, -11, -12, 5, 31, -28, 31, -72, 19,
  -34, -1, 54, 27, 18, -20, -11, 10, 58, 3, 28, -56, -11, 36, -66, 26, 14,
  -17, 84, 14, -3, 64]

theorem fractionalNearFrameSubtreeG1R0053_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0053Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0053Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0053Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0053_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0053LowerBoundTable : List ℤ :=
  [-34, -44, -18, -25, 168, 148, 1, 2, 2, -64, -21, 42, -140, -9, -41, 16,
  -123, -21, 96, 44, -75, 286, 10, 294, -281]

def fractionalNearFrameSubtreeG1R0053LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0053Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0053LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
