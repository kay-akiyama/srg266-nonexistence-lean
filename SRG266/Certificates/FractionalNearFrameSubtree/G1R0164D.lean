import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0164`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0164Mask : ℕ := 2368029967985673

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0164Witness : Array ℤ :=
  #[123, 1070, 272, -21, 0, 562, 1227, 1017, 1372, 723, 1222, 174, -944,
  -1156, -1364, -810, -715, -390, 499, -404, 217, -20, -718, 129, 113, -370,
  -158, -153, 236, 863, 987, 1450, 337, 872, 264, -488, 682, 0, -627, -814,
  557, -116, -245, -136, 10, 167, 630, -718, -103, 7, 212, -10, 45, 611,
  157, -284, -246, 935, -189, 280, -458, -347, 24, 315, -218, -297, -485,
  336, 360, 500, 300, 607, 277, 461, -370, -410, 0, -22, -725, -8, -42, 110,
  24, 719, 476, 4, -315, 647, -454, 1318, 669, -5, 980, 688, -159, 104, 559,
  -656, 596, 174, -763, -105, -154, -2, -503, -150, -338, -631, -65, -566,
  322, -184, -449, -31, -123, -711, 726, 949, 144, 489, -144, -1055, -288,
  -750, 309, 336, -269, -954, -439, -742, 88, 10, -229, 614, 270, 715, -171,
  55, 761, 23, -12, 563, -121, -17, -599, -164, -895, 198, -720, 499, -985,
  298, 568, -403, 158, 110, 237, 483, -559, 725, -75, 27, -97, 416, 210, 38,
  680, -435]

theorem fractionalNearFrameSubtreeG1R0164_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0164Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0164Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0164Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0164_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0164LowerBoundTable : List ℤ :=
  [-262, 32, 31, 31, 759, 733, 247, 32, 2037, 1681, -1965, -1742, 1024,
  1607, 653, 797, 99, 2335, 1622, 447, 1949, 1721, -61, 2017, 4125]

def fractionalNearFrameSubtreeG1R0164LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0164Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0164LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
