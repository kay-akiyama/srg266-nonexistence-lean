import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0375`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0375Mask : ℕ := 5737069969609866

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0375Witness : Array ℤ :=
  #[17, 61, -20, 136, 80, -97, 245, -69, -135, -486, -24, 195, 160, 198,
  210, 274, 95, 220, 130, 492, 125, -68, 179, 160, -14, -249, 30, 99, -125,
  -116, -31, 246, 60, 1, -72, 268, 314, -2, -97, -214, 55, 70, -89, 39, 144,
  260, 348, -198, -37, -27, -30, 13, 282, -186, -139, 239, -220, -98, -52,
  80, 248, 33, 33, 28, 402, 91, 370, -3, 93, -24, 43, -131, 7, 29, 495,
  -228, -60, 68, -301, -173, -181, 10, -182, -84, -102, -399, 167, -97,
  -124, -71, 23, 233, 77, -204, -80, 702, -299, -106, 96, 289, -69, -47,
  -37, -196, 236, 462, 424, -47, -88, 145, 252, 290, 62, -194, -132, -441,
  122, -513, -283, -43, 92, -239, 360, -262, 138, 65, -17, 83, 161, 4, 14,
  149, 94, -5, -153, 41, -38, 117, 58, -128, -6, 118, 192, 165, -137, 241,
  234, 334, 136, 1, 93, 60, 166, -41, -102, 135, -20, -5, -50, -23, 48, 140,
  -43, -29, 203, 192, 71, -8]

theorem fractionalNearFrameSubtreeG2R0375_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0375Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0375Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0375Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0375_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0375LowerBoundTable : List ℤ :=
  [285, 270, -32, 313, 328, 504, -6, 674, 488, 1098, 476, 832, 509, 1000,
  -539, 423, 468, 534, -448, 609, 508, 1455, 329, 882, 1077]

def fractionalNearFrameSubtreeG2R0375LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0375Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0375LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
