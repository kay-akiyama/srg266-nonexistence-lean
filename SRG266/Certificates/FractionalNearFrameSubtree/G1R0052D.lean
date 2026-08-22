import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0052`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0052Mask : ℕ := 665041067690505

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0052Witness : Array ℤ :=
  #[-40, 45, 77, 53, 82, 107, -91, -10, -33, -12, 0, 83, -83, -25, -77, -62,
  -34, 8, 78, -3, 72, -36, -15, -75, 12, -86, -22, -16, 29, -8, 90, 40, -51,
  15, 35, 117, 9, 0, -49, -66, -110, -106, -42, 50, 51, 12, -58, 47, 101,
  -3, 57, 68, -24, 7, -15, 20, -27, 65, 30, -25, -12, -17, -33, -42, -60,
  52, 30, -72, -56, 109, 47, 55, -29, 17, 14, -10, 18, 55, -47, 4, -71, -6,
  31, 42, -26, -92, -37, -56, -30, -37, -33, 10, 53, 5, -14, -41, -32, 55,
  -60, -38, -62, 80, 66, 44, -24, 33, 0, -53, 30, -11, 10, 57, 17, 25, -9,
  48, 21, -12, -18, 6, -16, -1, 21, 29, 46, -13, 25, -46, -50, -2, 125, 16,
  62, -31, -18, 16, 23, 66, 51, 12, 31, -29, -29, -43, 28, -35, -16, 38,
  -14, 42, 30, -74, 22, -78, 25, 9, 18, 25, 26, -63, -16, 37, 36, 17, -27,
  67, -11, -10]

theorem fractionalNearFrameSubtreeG1R0052_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0052Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0052Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0052Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0052_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0052LowerBoundTable : List ℤ :=
  [-44, 59, -18, 1, 1, 68, 1, 36, -91, -8, 38, 203, 92, 134, 189, 150, -19,
  34, 80, 317, 9, 111, 9, 88, -138]

def fractionalNearFrameSubtreeG1R0052LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0052Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0052LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
