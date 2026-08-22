import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0090`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0090Mask : ℕ := 936555774094092

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0090Witness : Array ℤ :=
  #[-352, -527, -689, -543, -593, 256, 410, 270, -688, -5, 487, -423, 429,
  163, -244, -296, -430, -142, -397, 105, 195, 97, -272, 452, 473, 62, 2,
  -320, 307, -55, -533, -594, 431, 220, 574, 578, -230, 121, 651, 118, 16,
  -393, -1024, -626, 919, 542, 20, 520, -196, 211, 120, -6, 260, 165, -614,
  864, 36, 508, 0, -510, 154, -27, 181, 1, -506, -317, 1467, 499, -379, -81,
  -534, 596, -291, 226, 300, -344, 374, 547, -60, -144, 139, -295, -718,
  237, 260, -912, -405, 767, 794, 20, -82, 239, 272, -92, 154, -430, -124,
  293, 661, 482, -73, -453, -255, -282, 172, -1187, -811, -1330, -76, -296,
  235, -380, 109, 584, 422, -710, -136, -725, 898, 133, 203, -432, -611,
  -370, -929, 601, -92, -93, -113, 328, 535, 51, -68, 67, 273, 422, 341,
  -172, 142, 97, 690, 508, 236, 162, -414, 303, -151, -44, 372, -772, -71,
  123, -27, 0, -554, 448, -285, 243, -132, 712, 207, 516, -118, 115, -98,
  11, -71, 639]

theorem fractionalNearFrameSubtreeG1R0090_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0090Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0090Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0090Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0090_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0090LowerBoundTable : List ℤ :=
  [-473, 549, -117, -212, -643, 32, -95, 571, 1771, -1469, 614, -2120, -441,
  100, -964, 99, 1610, 3002, -1084, 100, -979, 159, 100, 916, 2873]

def fractionalNearFrameSubtreeG1R0090LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0090Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0090LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
