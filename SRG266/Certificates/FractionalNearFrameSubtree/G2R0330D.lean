import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0330`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0330Mask : ℕ := 5402557374214824

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0330Witness : Array ℤ :=
  #[-54, -4, 167, 55, 52, -44, -1, 88, -20, 34, -57, -37, 126, -33, -15,
  -45, 107, 22, -1, 20, 33, 129, 89, -4, 17, -27, -42, 28, -74, 31, 36, -14,
  25, -98, 33, 29, 30, 92, 133, 67, 39, 19, 3, 70, -44, -104, 44, 12, 6,
  -66, 41, 38, 60, -10, 30, -18, 44, -18, -83, -34, -58, -161, -6, 63, 70,
  -64, -21, 2, -77, 16, 4, -66, -120, -67, -168, -3, 30, -99, 8, -116, 73,
  111, -58, 86, -13, 38, -120, 38, 66, 2, 77, 25, 41, 74, -2, 41, -7, 62, 2,
  15, 27, -146, -14, 36, 26, 51, -99, -35, -47, 9, -25, -43, -38, 100, -20,
  80, 12, -1, -46, -10, 19, -10, 53, 103, -98, -58, -95, -59, -163, -41, 30,
  -60, -5, 23, 10, -35, 64, -90, 99, 2, 70, 65, 69, 64, 79, 25, 39, 66, 74,
  8, 1, -17, 56, -102, 18, 9, -182, 46, 133, 8, 154, -5, -13, 77, -13, 44,
  -238, 10]

theorem fractionalNearFrameSubtreeG2R0330_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0330Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0330Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0330Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0330_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0330LowerBoundTable : List ℤ :=
  [-49, 38, 10, 73, 83, -22, 51, 2, 36, 10, 213, 411, 10, 108, 34, 10, 18,
  164, 416, -55, 183, 298, 10, -200, -66]

def fractionalNearFrameSubtreeG2R0330LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0330Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0330LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
