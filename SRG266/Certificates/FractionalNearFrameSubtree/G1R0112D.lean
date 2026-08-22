import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0112`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0112Mask : ℕ := 968488576729506

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0112Witness : Array ℤ :=
  #[-2056, -1696, -2133, -1967, -1269, -934, 579, 1103, 153, 701, 429, 1219,
  284, 1311, 1281, 620, 614, 1331, -131, -231, -448, -306, 56, 385, 501,
  707, 129, 569, -232, 128, -128, -416, -301, -23, 645, 38, 899, -340, 0,
  -31, 525, 447, 97, 709, -672, -140, 63, -506, 7, 69, 54, 613, -301, 167,
  207, 114, -59, 185, -410, -519, 18, 465, -348, 59, 34, 624, 369, 155, 288,
  407, 115, -101, -46, 354, 268, -1, 219, 359, -276, 238, 1490, 64, 94, 425,
  544, 525, -136, 226, 174, -70, -68, 1498, -137, -206, -85, 122, -295, -18,
  -82, -455, 1951, -460, 339, -175, -50, 197, 317, 413, -263, -1384, 426,
  103, 258, -280, 195, -336, 12, 71, -169, 204, -367, 554, 349, -399, -200,
  -1307, -418, -388, -1494, -393, 1960, -1422, -624, 284, 419, 215, -113,
  114, 466, 102, -57, 12, -5, -75, 35, -97, 508, 315, -144, -368, -357, 124,
  -107, -218, 11, 517, 70, -669, 245, 50, 276, 270, 603, 449, -254, 457,
  -444, 52]

theorem fractionalNearFrameSubtreeG1R0112_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0112Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0112Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0112Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0112_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0112LowerBoundTable : List ℤ :=
  [309, 89, 1001, 493, 772, 1671, 2078, 93, 34, -1968, 603, 394, 1209, 903,
  2855, 697, 417, 100, 1587, 100, -2584, 99, 602, 79, 3071]

def fractionalNearFrameSubtreeG1R0112LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0112Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0112LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
