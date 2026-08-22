import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0493`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0493Mask : ℕ := 5811293306082580

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0493Witness : Array ℤ :=
  #[-1118, -691, 607, 389, -866, 286, 168, 848, 484, -693, -74, 245, 1427,
  -476, 919, 793, -265, 117, 1195, 740, 672, -25, 648, 308, -214, 675, -484,
  -893, -391, 679, -980, -669, -368, -47, 250, 643, 1666, 590, 251, 68, 311,
  648, 447, 776, 435, -474, -239, 919, 288, 136, 553, 271, 171, 405, -27,
  -301, 519, 0, -143, 583, 775, -397, -33, -123, -1563, -225, -584, -336,
  59, 173, 791, 780, 165, 194, 145, -44, -538, -366, 70, 76, 918, 1445, 544,
  -920, -1067, -502, 903, -211, 447, 1317, -505, -97, 833, -599, 408, -509,
  361, 1202, 425, 978, -75, -77, -791, 433, 399, -238, -913, -46, 248, 1264,
  -23, 271, 584, 293, 288, -455, 247, 317, 600, 940, 556, 288, -874, 8,
  -175, -455, 990, -47, -990, 696, -40, 299, -225, -197, -1631, 321, 851,
  176, -320, 723, 255, -141, 29, 164, 407, 1047, -901, 454, 0, -462, 714,
  143, 201, 406, 1448, 446, 385, 244, 1040, -1051, -264, -502, -318, 552,
  -143, 1031, -483, -877]

theorem fractionalNearFrameSubtreeG2R0493_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0493Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0493Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0493Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0493_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0493LowerBoundTable : List ℤ :=
  [1301, 1530, -3, 1528, 1926, 1638, 1573, 1368, 1646, 668, 2255, 101, 3784,
  1243, 448, -1698, 189, 5715, 4084, 4218, 5432, 444, 3598, 1622, 2301]

def fractionalNearFrameSubtreeG2R0493LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0493Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0493LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
