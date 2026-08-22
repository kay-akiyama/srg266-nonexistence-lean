import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0528`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0528Mask : ℕ := 6780359527733793

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0528Witness : Array ℤ :=
  #[-733, 26, -466, -2261, 0, -2006, 1775, 840, 2659, 1347, 2233, 577, -30,
  447, 961, -576, 0, 1390, 79, -78, -85, -921, -131, 440, 407, 1961, -625,
  658, 304, -419, -809, 1701, 539, 633, 856, 708, -1158, -1026, 218, 431,
  967, 475, 1208, -1608, -146, -12, -389, -250, 80, 434, -160, 957, -3, 289,
  -124, 798, 549, -97, -209, -233, 387, 758, 162, 234, 35, 4, -252, 914,
  -276, -334, -157, 80, 355, -249, -279, 435, 542, 217, -545, 647, 462,
  -162, -13, 604, 27, 400, 82, -235, 874, -130, -14, -263, -454, 683, 992,
  34, -473, 827, 1038, 365, -471, 485, 529, -3, 419, -542, -76, 225, 114,
  -259, 627, -111, -226, -29, -789, 326, 504, 670, 913, -368, 75, 219, 914,
  -288, -304, 626, -371, 226, -155, -739, -840, -523, -491, 305, 431, -68,
  -538, 192, 290, 409, 172, 697, 0, 501, -129, -363, -1219, -1262, -680,
  150, 199, 108, -504, 446, 930, 418, 324, -788, 1253, 414, -86, 1371, -925,
  -555, 533, -1028, 653, -1817]

theorem fractionalNearFrameSubtreeG2R0528_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0528Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0528Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0528Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0528_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0528LowerBoundTable : List ℤ :=
  [1327, -644, 521, -213, 1227, 3058, 1779, 5572, 31, 99, 100, 533, 99,
  3805, 1376, 1374, 1545, -904, 3154, 2346, 1094, -387, 2002, 3892, 3963]

def fractionalNearFrameSubtreeG2R0528LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0528Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0528LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
