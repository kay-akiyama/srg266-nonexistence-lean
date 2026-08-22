import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0351`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0351Mask : ℕ := 5670678507932169

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0351Witness : Array ℤ :=
  #[-2061, -281, -455, -859, -207, -504, -104, 316, -71, 68, 1192, 74, 389,
  577, -11, 138, 18, 1115, 507, -763, -44, 555, -174, 232, 772, 320, -240,
  902, -10, -335, 8, -458, -1344, -20, -8, 399, -573, 419, 1317, 846, -218,
  263, -643, -1182, 1318, -1280, -1506, 626, 299, 636, -94, 1193, -131, 765,
  419, 524, 387, 986, 170, 393, -24, 256, 382, -1854, -73, 223, 349, -557,
  -507, -459, 387, -459, 337, 345, -563, -9, 87, 199, 348, 350, -115, 361,
  -394, 519, -2, 208, -469, 248, 337, 164, -1637, 489, 691, 148, -53, -312,
  336, 888, 64, 618, 720, -1021, 157, 250, 532, 467, 279, -346, 415, 116,
  -303, 547, -296, -809, -284, 700, -1011, 568, -190, 378, 178, 65, 900,
  -373, -463, -299, -140, -64, -428, -741, -64, -807, -238, 470, 254, -545,
  1012, 63, 357, 754, 260, 344, 977, -1077, -1502, 24, 737, 633, 449, -50,
  193, 1062, -251, -353, -372, 837, 334, -801, -916, 281, 833, 145, 273,
  -81, 307, 286, -237, -74]

theorem fractionalNearFrameSubtreeG2R0351_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0351Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0351Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0351Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0351_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0351LowerBoundTable : List ℤ :=
  [14, 523, 704, 32, 966, 1808, 33, -119, 33, 963, 1074, 1014, -132, 655,
  309, -456, 3007, -1269, 1685, 1331, 2368, 1497, 1735, 1035, 1074]

def fractionalNearFrameSubtreeG2R0351LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0351Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0351LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
