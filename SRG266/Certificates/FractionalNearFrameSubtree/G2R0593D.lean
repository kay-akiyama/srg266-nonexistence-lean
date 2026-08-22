import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0593`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0593Mask : ℕ := 6865860267066130

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0593Witness : Array ℤ :=
  #[1358, 790, 736, 702, 565, 256, -447, -518, -94, -1117, 47, -14, 1139,
  -30, 829, -1009, -9, 831, -335, 159, 1009, -474, -165, 1152, -644, -113,
  -26, -1247, 337, -191, 773, -323, 118, 939, 486, -1169, -555, -327, 333,
  707, 244, 1267, -1881, -1068, 421, 178, -357, 589, -828, -1154, 156, 845,
  -885, -324, -1097, 1616, 424, 169, 90, 822, 13, -470, 407, 63, -84, 187,
  254, -264, -430, -491, 570, 152, 493, -1287, 156, 392, 757, -723, 355,
  -1017, -151, -103, -698, 819, 620, 459, 218, 298, 251, -260, -392, 16,
  510, -210, 219, 270, -569, -427, 355, -485, 326, 319, -1529, 401, 425,
  197, 71, -927, -278, 390, 948, 1025, 68, -638, 159, -128, -790, 1084,
  -345, -140, 145, 325, 1037, 64, -334, 55, -506, -602, 987, 969, 92, 485,
  521, 627, 136, 25, -618, 565, -1942, 1268, -183, -514, 241, -554, -780,
  983, 399, -161, -425, 301, -775, 395, 1331, 397, -714, -452, 486, -90,
  -460, -197, 255, -62, 461, 226, 444, -458, -334, 147]

theorem fractionalNearFrameSubtreeG2R0593_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0593Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0593Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0593Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0593_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0593LowerBoundTable : List ℤ :=
  [-500, 31, 298, 161, -892, 1038, 301, 1379, 276, -886, 883, 2880, 201,
  1132, -244, -943, 933, 1594, 4178, 4146, 3366, -1552, 100, -303, 2703]

def fractionalNearFrameSubtreeG2R0593LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0593Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0593LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
