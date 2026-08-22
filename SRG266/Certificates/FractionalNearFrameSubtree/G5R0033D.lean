import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0033`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0033Mask : ℕ := 1391241688219715

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0033Witness : Array ℤ :=
  #[-322, -355, 797, 408, -377, 42, 0, 137, 105, -610, -561, -19, 0, 20,
  -128, -176, -219, -410, 883, 265, 14, 388, -1, -97, -52, -680, -845, 72,
  102, -14, -191, 131, -947, -860, -103, -525, -934, -811, 0, 569, 433, 697,
  161, 14, 111, 337, 474, 110, -45, 51, 278, 508, 373, 362, 159, 31, -268,
  -398, 94, -29, 454, -89, 192, 250, 367, -294, 1629, -135, -274, -118,
  -462, -601, -583, -551, -558, -543, -364, -420, -168, -270, -49, 106, -56,
  132, -161, -225, -437, 97, 361, 303, 955, 625, -119, -172, 35, 118, -263,
  145, -517, 319, 325, -337, -38, -178, 201, 562, 471, 317, 31, 0, -209,
  -427, 303, 344, 58, -97, -558, -70, -116, -222, 441, -785, 127, -27, 431,
  264, -355, -634, 0, 28, 284, 191, -25, -414, 588, -109, 423, -164, 45,
  -835, 507, 60, 351, 0, -40, -176, 737, 556, 582, 465, 639, 441, 449, 271,
  -126, -443, -69, 88, 10, 197, 0, -107, 326, 103, 446, 472, 117, -155]

theorem fractionalNearFrameSubtreeG5R0033_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0033Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0033Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0033Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0033_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0033LowerBoundTable : List ℤ :=
  [-385, 1139, -405, -86, 212, 322, -684, 383, 387, 1347, -337, 2184, 2046,
  -791, 586, -2278, -560, 1986, -1226, 11, 15, 253, 479, 848, 24]

def fractionalNearFrameSubtreeG5R0033LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0033Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0033LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
