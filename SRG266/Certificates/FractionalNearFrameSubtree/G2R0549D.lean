import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0549`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0549Mask : ℕ := 6839772618925578

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0549Witness : Array ℤ :=
  #[-187, 92, 106, -266, -84, 210, -120, -10, -70, 58, 199, -246, 32, 16,
  -120, -128, -152, -151, 342, -205, -393, -314, 69, 46, -107, 103, 325,
  351, 223, 240, 89, -109, 155, 26, 122, -9, -97, -128, -109, 244, 296, 156,
  400, 145, 75, 81, 34, -101, -18, -35, 24, 19, 46, -45, 397, 270, 554,
  -290, 123, -194, -369, -331, -109, -30, -27, -259, -149, -304, -161, -187,
  83, 40, 102, -28, -205, 140, 132, -41, 78, -49, 28, -14, 31, -61, 280, 57,
  -38, 105, -52, 223, 60, 90, 79, 36, 107, -90, 55, 77, -16, -57, -77, 67,
  -14, -38, 60, 92, -116, -213, 172, 12, 295, 262, 52, 147, 20, -74, -101,
  -38, -37, -54, 206, 132, 121, -92, 132, 82, 182, 137, 73, 93, -48, 152,
  228, 96, 67, -163, 172, 172, -47, 96, 56, 306, 122, 11, 364, 504, -72,
  221, 16, 105, -254, -65, -31, 58, -12, -12, 0, 134, -58, 12, 229, -103,
  -115, 8, 143, -73, -180, -14]

theorem fractionalNearFrameSubtreeG2R0549_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0549Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0549Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0549Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0549_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0549LowerBoundTable : List ℤ :=
  [259, 670, 349, 224, 574, 426, -46, 2, -54, 672, 769, 832, 442, 557, 533,
  151, 170, 120, 945, 560, -220, 595, 210, 9, 801]

def fractionalNearFrameSubtreeG2R0549LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0549Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0549LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
