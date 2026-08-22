import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0061`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0061Mask : ℕ := 953996294079114

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0061Witness : Array ℤ :=
  #[29, -36, 19, 10, -58, 58, -32, -24, -40, -52, 35, 71, 40, 26, 0, 60, 26,
  -49, -5, 0, 34, 23, 25, 33, -39, -57, 22, 21, 7, -59, -37, -56, -12, 51,
  54, 21, 15, -34, -18, -35, -16, 17, -68, -35, -92, 7, 8, 32, 86, 102, -25,
  -16, 26, 63, 2, -10, 23, -14, -16, 42, 31, 8, -2, 30, 72, 98, -38, -11,
  11, -22, -36, -18, -30, -75, -58, -25, 8, -20, -74, -57, 24, 53, -2, 21,
  40, 54, 19, 14, 6, 7, 42, 34, -10, -66, -23, -50, 81, -20, 43, -47, -74,
  -14, -21, -12, -35, -16, 55, 79, 25, 24, -8, -7, 21, 44, 24, -34, 16, 65,
  16, -17, 6, 116, 11, 11, -6, -4, -33, -23, -8, -40, -39, 25, 9, -7, -79,
  23, -56, -5, 89, -50, 69, 26, -35, -21, 49, -7, 2, -21, 66, -116, -63,
  -31, -16, 2, 34, 14, 33, 32, 112, 82, -47, -83, 33, 81, -9, 19, 26, 64]

theorem fractionalNearFrameSubtreeG2R0061_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0061Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0061Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0061Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0061_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0061LowerBoundTable : List ℤ :=
  [-25, 85, 2, 2, -59, 135, 32, 32, 11, 238, 164, -81, 114, 101, 73, -56,
  10, 86, 169, -56, 9, 161, 180, -88, 138]

def fractionalNearFrameSubtreeG2R0061LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0061Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0061LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
