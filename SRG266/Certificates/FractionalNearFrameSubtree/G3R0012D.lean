import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0012`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0012Mask : ℕ := 747317401131537

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0012Witness : Array ℤ :=
  #[-827, -1212, -1382, -1753, -1820, -1868, 1151, 326, 853, 653, 130, 293,
  1297, 527, 1032, 711, 438, 293, -119, -372, -12, 57, 0, 868, 330, 220,
  364, 340, -271, -690, -983, -930, -225, -349, -201, -277, -26, 869, -243,
  -653, 188, 169, 426, 392, -757, -738, 41, 227, 1360, 332, -160, 306, 206,
  -442, -273, -5, -186, -433, -44, 1420, 266, 97, 248, 193, 357, 94, 366,
  -193, 371, -54, 253, 140, -149, 286, 79, -206, -136, -89, 64, -8, -229,
  302, 25, -468, 98, 34, 581, 181, -235, 15, 41, -406, -66, -22, -404, 138,
  514, -611, 741, -385, -640, 692, -549, 74, 177, -1007, -1077, -1184, -695,
  -1013, -743, -1175, -754, 1977, 1978, -45, -46, 35, 508, 67, -154, -181,
  292, 0, 87, -382, 186, -192, -212, 286, 353, 192, -19, 326, 70, 27, -201,
  11, 442, 645, 81, -245, -80, -3, 158, -524, 74, 833, -246, 337, -113, 62,
  -68, 1, -17, -105, 204, 248, -451, 323, 310, 252, -349, 139, 109, 779,
  114, 99]

theorem fractionalNearFrameSubtreeG3R0012_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0012Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0012Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0012Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0012_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0012LowerBoundTable : List ℤ :=
  [-434, 672, 32, 377, 31, -557, -240, 32, 980, 98, 522, 131, 100, 1717, -6,
  -578, -1176, 1851, 35, 73, -1240, -705, 99, 875, 272]

def fractionalNearFrameSubtreeG3R0012LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0012Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0012LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
