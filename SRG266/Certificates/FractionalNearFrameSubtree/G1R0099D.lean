import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0099`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0099Mask : ℕ := 952003435545350

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0099Witness : Array ℤ :=
  #[110, 82, 119, 45, 47, 97, 0, 28, -18, -20, 45, 88, -161, -63, -125,
  -129, -165, 83, 25, -52, 7, -55, 65, -4, 35, -23, -20, 63, -7, 63, 170,
  -17, 50, -59, 3, 54, -15, -80, 72, 35, 22, -134, -128, -32, -70, -70,
  -178, 68, 77, -8, 29, 27, 68, 5, -27, -141, 77, -68, -44, 24, 1, -53, -11,
  41, 0, -87, 81, 33, -12, -62, 51, -16, -28, 44, 56, -10, -139, -38, 65,
  -16, 99, -19, 19, 70, 169, 47, -140, 36, 1, 71, 21, 40, 94, -9, -14, 64,
  39, -25, -67, -20, 43, -70, -16, -69, 26, 26, -232, 61, 44, -75, 8, 0, 0,
  -112, 3, 111, 40, 78, -17, -2, -29, 35, -63, -50, 104, -23, 21, 22, 19,
  -22, 75, -19, 2, 23, 158, 159, -10, -133, -47, 13, 40, 58, 138, 123, 40,
  32, -21, 55, -3, -35, -19, -64, 22, 72, 19, 102, -1, -39, 18, -9, -144,
  88, -41, 42, 18, 116, -165, 111]

theorem fractionalNearFrameSubtreeG1R0099_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0099Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0099Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0099Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0099_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0099LowerBoundTable : List ℤ :=
  [-8, 195, -86, 87, 52, 23, 2, 0, 110, 151, 294, -99, 192, -94, 270, 235,
  10, -1, -39, 10, 253, -62, 381, 85, 151]

def fractionalNearFrameSubtreeG1R0099LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0099Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0099LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
