import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0369`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0369Mask : ℕ := 5716126620785816

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0369Witness : Array ℤ :=
  #[1603, -120, 1179, 791, -219, -480, 901, -276, -1002, 347, 7, 711, -523,
  408, 2155, -712, -304, 353, 386, -2088, -600, -626, 2088, 276, -1051,
  1231, 2323, 799, 2035, 243, 395, 602, 1528, -672, 664, -820, 307, -1322,
  -852, -205, -636, 876, -773, -513, 619, 1048, 1053, 1514, -971, 21, -974,
  2461, -420, -185, 1476, -833, 21, -80, 1488, 126, 705, -180, 1848, -880,
  804, -299, -79, 1305, 728, -5, 948, 0, 296, 1219, -2660, -1237, 1186,
  -695, 815, 1529, -164, -416, 1129, 1686, -1276, 1219, 15, -512, -814, 416,
  397, -413, 260, 98, 1296, -252, -503, -234, 200, 273, 106, -47, 2385, 960,
  199, 951, -563, -365, -119, 585, -705, 2379, 1117, -642, -730, -1914,
  -632, -372, 1104, 608, 681, 1896, 1451, 1112, 1995, 1264, -1056, 337, 793,
  644, -565, -753, 1523, 868, 509, 338, 1443, 633, -587, 599, -1004, -512,
  2539, 831, -550, 1617, -1062, -250, 475, -851, 1712, 1613, -509, 911, 875,
  329, -561, -880, -752, 1037, -642, 0, -413, -145, 1240, -1312, -232, -496]

theorem fractionalNearFrameSubtreeG2R0369_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0369Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0369Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0369Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0369_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0369LowerBoundTable : List ℤ :=
  [2335, 2607, 890, 2313, 4791, 1551, 1721, 4647, 3474, 2544, 6428, 5355,
  4820, 4031, 4544, 3658, -4065, 5101, 2178, 2169, 2827, 9216, 8600, -4348,
  5416]

def fractionalNearFrameSubtreeG2R0369LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0369Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0369LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
