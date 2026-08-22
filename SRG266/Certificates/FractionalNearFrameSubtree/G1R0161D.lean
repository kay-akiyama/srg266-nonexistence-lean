import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0161`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0161Mask : ℕ := 1871108502030704

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0161Witness : Array ℤ :=
  #[-245, 40, 50, 216, 179, 86, 138, 126, 39, -58, 72, -103, 22, -128, -179,
  113, -9, 169, -103, 169, 76, -43, 51, -100, 62, 5, 7, 420, -11, -80, 20,
  -176, -123, 8, 134, 308, 185, 24, 118, 432, 462, 14, 24, 20, -116, 275,
  -170, -184, 271, 201, 335, 207, -254, -224, 137, -181, -24, 234, -249, 82,
  6, 73, -13, 355, -79, -42, 348, -96, 5, 118, -145, -87, -21, -47, 146,
  -148, 116, 288, 33, 163, 170, 92, -285, -147, -96, 109, -355, 293, 24,
  431, -122, 6, -150, -299, 104, -153, 29, 239, 448, 29, 63, -244, 227, 0,
  326, 181, 55, 135, -116, -149, 174, -18, 18, 125, 237, 318, 156, 48, 84,
  61, 125, -168, -380, -141, 1, 18, 118, 27, 195, -305, -19, -174, 116, -84,
  110, 199, 315, 54, -89, -149, -54, -180, 104, 118, 130, 44, 239, -43, 46,
  110, 26, 189, 52, 216, -260, -124, 92, 273, 40, -7, -175, -172, -177, 216,
  -3, -180, 266, -191]

theorem fractionalNearFrameSubtreeG1R0161_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0161Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0161Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0161Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0161_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0161LowerBoundTable : List ℤ :=
  [319, 206, 86, 582, 363, 557, 155, 416, 543, 360, 584, 287, 80, 443, -157,
  261, 578, 1885, 424, 642, 686, 636, 1308, 653, 330]

def fractionalNearFrameSubtreeG1R0161LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0161Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0161LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
