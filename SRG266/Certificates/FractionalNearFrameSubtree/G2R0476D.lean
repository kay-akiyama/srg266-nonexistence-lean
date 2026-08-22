import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0476`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0476Mask : ℕ := 5809447543647384

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0476Witness : Array ℤ :=
  #[-466, 324, 85, 159, -92, 426, 163, 574, 766, 560, -307, -323, -292, -64,
  -398, 261, -191, -223, -216, -46, 122, -2, 66, 603, 232, -248, -163, 571,
  -279, -340, -756, -132, -96, 345, 959, -536, 75, -88, 1148, 477, 454, -67,
  85, 193, 21, -479, -670, -487, 242, 179, -116, -473, 274, -70, -689, -519,
  -626, -178, 138, -293, -459, 108, -163, -157, 330, -253, 0, -605, -270,
  -100, -175, -334, 48, -244, 346, -401, 179, 142, 0, 52, -200, 38, 40,
  -123, -56, 402, 193, 77, 544, -18, 53, 667, -125, -26, 537, 265, -54,
  -124, 299, 74, 490, 444, -229, 655, -254, 447, 164, 487, -203, -29, 587,
  -92, 167, 91, -194, -870, -50, 360, -379, -42, 154, 298, -497, 173, -141,
  295, 299, 464, -260, 77, 95, 101, 121, 91, -68, -796, 124, 377, -147, 240,
  309, -465, -249, 415, -598, 0, -717, -25, -410, -330, -348, 158, 52, 19,
  -39, 360, 95, 663, 544, -541, 250, 327, 207, -296, 317, 53, 121, 139]

theorem fractionalNearFrameSubtreeG2R0476_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0476Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0476Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0476Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0476_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0476LowerBoundTable : List ℤ :=
  [-433, 341, 865, 635, 828, -82, -1729, 11, 95, 1558, -1729, 423, 583,
  1872, -244, 221, 1115, 1652, 1002, -412, 342, 467, 331, -1831, 1204]

def fractionalNearFrameSubtreeG2R0476LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0476Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0476LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
