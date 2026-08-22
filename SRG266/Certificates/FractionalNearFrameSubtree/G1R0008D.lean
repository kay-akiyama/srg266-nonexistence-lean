import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0008`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0008Mask : ℕ := 260472328472721

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0008Witness : Array ℤ :=
  #[1236, -383, -707, 88, -1559, -76, 987, 584, 896, 482, 461, 1795, -1217,
  0, -576, -1152, 1118, 1186, 802, 232, 229, -682, -1922, 1634, -486, -1092,
  -895, -216, 2176, 53, 755, -24, -509, 520, -1914, 0, -150, 789, 832, 272,
  -1053, -228, -937, 773, 510, 779, 359, 1211, -2110, -68, 459, 1316, 916,
  -304, -215, -125, -1654, 609, -820, 299, 25, -1277, 876, 388, 413, -2065,
  717, -146, -58, -63, -521, 204, -538, -438, 2, 875, 906, 284, -530, -198,
  -147, -694, -798, 835, 433, -178, -16, 571, -1183, 515, -192, 405, 196,
  1361, 804, 1678, 2087, 1301, 318, -312, -496, -81, 685, 813, -285, 21,
  1009, -563, -703, 125, 291, -70, 995, 365, -123, -999, 647, -77, -19, 285,
  939, -64, -116, -584, -516, -1003, 169, -448, 848, -761, -978, -762, 1244,
  942, -211, 108, -207, 70, 432, 1709, 772, -1232, -727, 262, -255, 56, -94,
  -241, -461, -949, -948, 476, 615, -1111, -1120, -393, 1115, 526, -1689,
  499, -90, 659, 297, 1445, 348, 166, -1921, -1344]

theorem fractionalNearFrameSubtreeG1R0008_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0008Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0008Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0008Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0008_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0008LowerBoundTable : List ℤ :=
  [-1220, -1881, 336, -1768, 1968, 1921, 510, 32, 669, 98, 2921, 990, 2978,
  735, -894, 2057, 129, -287, 47, 3090, 434, 5689, 98, 1910, 101]

def fractionalNearFrameSubtreeG1R0008LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0008Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0008LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
