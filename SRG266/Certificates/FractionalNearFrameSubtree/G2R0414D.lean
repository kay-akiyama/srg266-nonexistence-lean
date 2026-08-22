import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0414`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0414Mask : ℕ := 5748611630715288

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0414Witness : Array ℤ :=
  #[5, -36, -1, -13, -62, -37, -41, -4, 5, -4, 67, 90, 18, 18, 28, 56, 67,
  30, 36, -31, -19, 68, 56, 40, -103, -171, -98, -64, -10, -47, -60, -12, 8,
  -3, 77, -60, -21, -30, 11, 27, 49, 76, 40, 42, -48, -70, -12, -27, -14,
  -55, 41, -35, -2, -38, -74, 44, -52, 18, 87, 13, 12, -40, -46, 94, 97, -9,
  -51, 9, 29, 79, -76, 7, 11, 35, 37, 62, -7, -11, -27, 37, -3, -12, -74,
  -57, 4, 16, 62, -5, 97, -51, -8, 48, 3, -74, 94, 48, 57, -9, 10, 13, -30,
  62, -50, 12, 59, 6, -66, 21, 14, -3, -46, 46, 94, 10, 2, -10, -59, -43, 8,
  63, 18, 99, -34, -38, -3, 7, 39, 34, 16, 57, 16, 25, -26, 57, -21, 5, -35,
  56, -21, 16, -12, -49, 0, -121, -30, -7, -5, 78, 15, -18, 27, -25, -15,
  60, 33, -25, 77, 86, -17, 38, -29, -9, 9, 112, 109, 45, 6, 6]

theorem fractionalNearFrameSubtreeG2R0414_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0414Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0414Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0414Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0414_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0414LowerBoundTable : List ℤ :=
  [-12, 100, 114, 72, -24, 30, 1, 1, -25, 410, 10, 130, 51, 261, 119, 6,
  167, 204, 312, 94, 131, 123, -55, -5, 62]

def fractionalNearFrameSubtreeG2R0414LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0414Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0414LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
