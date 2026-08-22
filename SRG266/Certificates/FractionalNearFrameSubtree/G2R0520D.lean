import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0520`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0520Mask : ℕ := 6764086785907217

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0520Witness : Array ℤ :=
  #[-2, -267, -191, 0, -159, -691, -14, 204, 478, 21, 218, 434, -9, 255,
  802, 292, 387, 917, 465, 172, 431, 240, 339, -138, 44, 226, -1, 138, -628,
  -209, -603, 524, 345, 45, 269, 208, 231, -133, -45, -343, -354, 97, 277,
  395, -583, 601, 5, 0, -286, 147, -49, 93, 46, 65, -863, 36, 24, 410, -244,
  -174, -265, -340, 2, 252, 26, -52, -287, 110, 325, 176, -97, -315, -508,
  227, 324, 6, -264, 322, 299, 774, 221, 82, 217, 184, 128, -178, 264, 72,
  -80, 489, 11, 181, -9, -167, -134, 515, 29, -146, -8, 1207, -45, 299, 75,
  61, 66, -134, 197, -119, 480, -679, -614, 195, 115, -832, 278, -678, 183,
  1391, -206, -8, 362, -29, 402, -164, 297, 323, 424, -68, 20, -163, 56,
  369, 392, -19, -378, -75, 516, -145, 149, 143, -222, -76, 107, -253, -93,
  -323, 467, -287, -349, 81, -99, 464, 32, -198, -319, -268, 47, 735, -76,
  223, 462, 11, 187, 189, -514, -363, -220, -722]

theorem fractionalNearFrameSubtreeG2R0520_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0520Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0520Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0520Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0520_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0520LowerBoundTable : List ℤ :=
  [515, -212, 31, 33, 1884, 71, 1320, 1719, 30, 805, 1634, 1562, -61, 2181,
  717, -349, 354, 1378, 88, -375, 775, 1820, 1440, -43, 101]

def fractionalNearFrameSubtreeG2R0520LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0520Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0520LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
