import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0237`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0237Mask : ℕ := 5108012005575177

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0237Witness : Array ℤ :=
  #[93, 359, 665, -303, 1010, -181, 869, -585, 297, -86, 0, 361, 195, 403,
  0, 592, 1, -921, 641, -867, -416, 161, 121, 447, -624, -697, -109, -682,
  556, 590, 1599, 967, -115, -26, 63, 106, 319, 56, 161, -158, -262, 44, 26,
  -186, -131, 100, -218, 610, 722, 201, 116, -318, 631, 7, -107, -371, -130,
  230, 111, -26, 410, 304, 155, -58, -18, 454, -227, -335, -411, -214, 103,
  110, 32, 318, 266, 4, 71, 295, -173, -198, 194, -56, 446, -131, 7, 31,
  -209, -29, 243, 729, -31, 140, 213, 290, -145, -18, -363, -172, -85, 397,
  -174, 738, -22, 232, 166, -470, -487, 167, 364, 193, 86, 88, 97, -113,
  102, -97, 91, -48, 297, -110, -153, 106, 20, -316, -531, -629, 259, 354,
  192, 668, -33, 156, -525, 220, -250, 247, -309, -208, 30, -122, 202, 263,
  -361, -523, 342, -306, 497, 122, 336, 142, 422, 10, 195, 791, 18, 222,
  -395, 247, -5, -215, -308, -5, -268, 32, 460, 555, 64, -52]

theorem fractionalNearFrameSubtreeG2R0237_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0237Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0237Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0237Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0237_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0237LowerBoundTable : List ℤ :=
  [657, 624, -393, 197, 1030, 1111, 31, 2984, 1926, 1261, 1272, -476, 101,
  419, 720, 707, 99, 862, 100, 1253, 751, 98, 1822, -49, 2137]

def fractionalNearFrameSubtreeG2R0237LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0237Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0237LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
