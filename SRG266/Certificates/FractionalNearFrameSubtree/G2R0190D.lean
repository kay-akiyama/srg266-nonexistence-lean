import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0190`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0190Mask : ℕ := 1393678642299496

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0190Witness : Array ℤ :=
  #[513, 806, -581, 553, -299, 195, 88, 241, 149, 38, -68, -113, 28, 275,
  367, 696, 2, 695, 231, 74, -95, -12, 352, -172, -349, -1503, -260, -121,
  179, -183, 62, 375, -88, 379, 476, -724, -693, 0, -849, 104, 540, 180,
  -294, 893, 254, -10, 1296, -771, -508, -336, 244, 68, 1236, -1701, -480,
  -797, -369, 215, 119, 156, 229, 695, -394, 86, 133, 347, 141, 269, -87,
  -103, 345, 98, 512, -191, 530, 893, 366, -28, 249, 824, 693, -801, 190,
  -181, 114, -169, 552, 535, -1155, -428, 29, 791, -650, -535, -332, 145,
  72, 671, 578, 718, 297, -762, -50, 767, 342, -27, -672, -220, 63, -601,
  87, 274, 37, -66, -180, -217, -274, 299, 338, -86, -49, 314, 479, -59,
  171, -693, 513, 126, 458, -1, -192, 655, -623, 407, 556, -787, 292, -171,
  -2059, -1052, -119, 750, -1192, -253, 463, 495, 512, 380, -757, 104, -380,
  526, -1024, -522, -420, 307, -274, -235, 158, 121, 1047, 570, 525, 111,
  1508, -434, 351, 58]

theorem fractionalNearFrameSubtreeG2R0190_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0190Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0190Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0190Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0190_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0190LowerBoundTable : List ℤ :=
  [-204, 33, 953, 32, 702, 516, 955, -522, 747, 2345, 94, -620, -577, 2077,
  -109, 115, -684, 815, 205, 167, 2594, 2535, 3091, 298, -34]

def fractionalNearFrameSubtreeG2R0190LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0190Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0190LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
