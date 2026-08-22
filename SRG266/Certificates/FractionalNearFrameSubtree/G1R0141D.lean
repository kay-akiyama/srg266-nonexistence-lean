import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0141`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0141Mask : ℕ := 1039413781058836

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0141Witness : Array ℤ :=
  #[266, -333, 1168, 617, -57, 214, 157, 530, -807, -780, 9, 345, 379, 177,
  -41, -726, 653, -5, -472, 177, 576, 376, 53, -206, 572, 124, 80, -81, -2,
  249, -38, -573, 42, 352, 115, -215, 321, -138, -161, -69, -130, -518,
  -374, -157, -75, 503, 265, 425, 929, 243, 294, 609, -208, 339, -11, -24,
  552, 0, -348, -299, -365, -517, -249, 114, 94, -36, -354, 447, -133, 220,
  460, 149, -622, -544, 457, 648, 50, 849, 41, -42, 323, -88, 190, 388, -79,
  97, -226, 698, 760, 217, 397, 754, 729, -229, -838, -102, 228, 91, 452,
  952, 66, 67, -378, 315, -600, 105, -238, -218, -433, -281, -103, -327,
  801, 424, 933, 244, 487, 64, 195, 127, 248, 617, -600, -831, 258, -183,
  -523, -47, -409, 5, 336, 397, -1109, 268, -49, -678, 784, -318, 0, 581,
  -604, -280, 478, 474, -197, 171, 1295, 85, -634, 660, 752, 686, 429, 350,
  250, -99, 177, -340, 364, 447, 71, -401, 62, 325, -34, -32, -450, 600]

theorem fractionalNearFrameSubtreeG1R0141_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0141Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0141Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0141Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0141_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0141LowerBoundTable : List ℤ :=
  [741, 890, 333, 1449, 1354, 787, 1372, 614, 827, 1354, 167, -283, 1068,
  -127, 1833, 1235, 633, 3533, 2186, 1466, 3976, 1270, 214, 2029, 1434]

def fractionalNearFrameSubtreeG1R0141LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0141Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0141LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
