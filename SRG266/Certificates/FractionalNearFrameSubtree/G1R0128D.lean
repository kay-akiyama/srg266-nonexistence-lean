import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0128`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0128Mask : ℕ := 970610544519600

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0128Witness : Array ℤ :=
  #[-27, 100, 175, -75, -67, 139, -7, 78, 151, -83, 109, 68, -101, -41, 98,
  252, 93, 56, 35, 77, 10, 57, -100, -108, 47, 34, 30, -61, -141, -173,
  -136, 26, -33, 229, 126, 195, -175, -51, 56, -69, 48, 99, 206, 18, 109,
  59, -102, -103, -68, 56, -2, 57, -58, -302, -3, 122, -35, -20, 92, 124,
  72, -62, -30, -75, -111, -175, -159, 107, 73, 11, 161, 180, 22, -18, 64,
  146, -42, 234, 52, 161, 22, 73, 37, 26, -162, 199, 115, 138, 93, 54, 15,
  -17, 235, -45, 56, 108, 112, 72, 22, 145, -15, 36, -103, -49, 131, 37, 75,
  -76, -60, -56, 58, 0, -31, 41, -1, -48, -127, -70, -76, -94, -58, -64,
  114, 13, 106, 13, -108, 104, -24, 58, 21, 76, -128, -61, -83, -139, 56,
  -1, -102, 23, 67, -134, -25, 44, 3, 33, -11, 76, 73, 43, 123, 204, 65,
  -185, 131, -59, 60, 197, 81, -154, -25, 36, 92, -109, -20, 4, 151, 243]

theorem fractionalNearFrameSubtreeG1R0128_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0128Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0128Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0128Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0128_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0128LowerBoundTable : List ℤ :=
  [121, 140, 67, 207, 183, 359, 274, 440, 70, 296, 132, 11, -224, 234, 7,
  186, -469, 412, 686, 834, 847, 327, 760, 258, 502]

def fractionalNearFrameSubtreeG1R0128LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0128Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0128LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
