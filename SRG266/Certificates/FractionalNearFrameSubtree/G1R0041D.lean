import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0041`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0041Mask : ℕ := 538379273479244

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0041Witness : Array ℤ :=
  #[52, 127, 101, 116, 38, 40, 13, -31, -60, -80, -42, -115, -110, -56, 15,
  -32, 53, -35, -63, 11, 18, 68, 42, -57, -25, 25, 27, 96, -17, -8, 1, -31,
  0, 3, 108, 102, -77, -77, -6, -31, 49, 77, -2, -64, -64, 127, 58, 100, 59,
  -62, 56, -77, -67, 57, 41, 32, 138, -93, 112, -60, -41, 70, -40, -10,
  -125, -5, -58, 24, 54, 95, -61, 7, -30, 15, -42, -22, 136, 12, -4, 87, 6,
  58, 102, -114, -33, 81, 86, -82, -85, 66, 7, -110, -86, 105, 150, 97, -53,
  76, 89, -15, 18, 39, -46, -1, 59, -9, -17, -46, -56, 88, 46, 55, 125,
  -169, -87, -89, -38, -59, -120, 38, -115, -98, 68, -27, 37, 32, 13, 12,
  -60, 18, -54, -67, -60, 2, -1, -31, -27, 45, -7, -10, -73, -66, -17, 35,
  -35, 131, 88, 16, 10, 83, 13, -65, 136, 36, 87, 46, -6, -11, 1, 3, -5, 52,
  10, 53, 128, 69, 37, 17]

theorem fractionalNearFrameSubtreeG1R0041_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0041Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0041Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0041Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0041_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0041LowerBoundTable : List ℤ :=
  [-24, 33, 27, 121, 6, 1, 131, 84, 141, 14, -13, 24, 140, -134, 228, 264,
  -55, 316, -29, 387, 285, -159, 142, 135, 422]

def fractionalNearFrameSubtreeG1R0041LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0041Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0041LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
