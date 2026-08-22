import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0463`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0463Mask : ℕ := 5807430006641298

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0463Witness : Array ℤ :=
  #[563, 330, 646, 635, 32, -332, 449, 53, 1107, 0, 100, 243, 40, -159, 456,
  -825, -49, 815, 413, 766, -104, 179, -454, -56, 265, -334, 95, -195, 382,
  233, 214, 755, 267, 747, 467, -201, 45, -225, 119, 326, -736, -455, 401,
  362, 287, 557, 536, -395, -668, 314, -337, -123, 341, -153, 0, 159, 272,
  -128, 523, 201, 113, -61, 307, -347, -23, -641, -271, -331, 97, 390, 630,
  -60, 70, -39, -145, 734, 131, -439, -261, 473, -98, 360, -217, -144, -173,
  -56, 589, -180, -1057, -257, -8, -141, 511, 524, 205, 462, -108, -477,
  703, 41, -47, 391, 54, 346, 380, 229, 714, -385, -128, 176, -30, 71, -170,
  -728, -442, 163, -416, -121, -367, 27, 731, 1069, -354, 446, 789, -62, 5,
  556, 501, 832, 353, 747, 114, -437, 1006, 441, 75, -110, -972, -439, 438,
  351, 90, 212, 508, 645, 364, 497, -64, -231, 409, 526, -90, -64, 289, 206,
  189, 350, 55, 631, 544, -124, -145, -209, 547, 452, 239, 328]

theorem fractionalNearFrameSubtreeG2R0463_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0463Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0463Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0463Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0463_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0463LowerBoundTable : List ℤ :=
  [1150, 1876, 1225, 1870, 1325, 951, 1908, 1371, 1993, 1823, 1360, 1256,
  3354, 3509, 710, 593, 546, 252, 3234, 1185, 3187, 366, 1803, -319, 916]

def fractionalNearFrameSubtreeG2R0463LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0463Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0463LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
