import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0139`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0139Mask : ℕ := 6498424412801392

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0139Witness : Array ℤ :=
  #[177, -9, 791, 506, -104, 349, -231, -167, 617, 367, -400, 1146, 821,
  -399, 344, 462, -23, 557, 187, 876, 421, -244, 367, 580, 131, 221, -1340,
  250, -108, 95, -253, -434, 371, 123, -250, -191, 99, 65, 473, 192, -698,
  -399, 772, -305, -439, -143, 782, 16, -331, -687, -151, -864, -534, -262,
  -64, -261, -461, 432, -605, 909, -82, -494, 785, -148, -42, 301, 115,
  -404, -1382, -406, -117, 38, -97, 0, 418, 489, 567, -135, -51, -247, 472,
  383, 66, 775, -136, 163, 4, -288, -737, -112, 472, 302, 72, -264, 962,
  756, 420, -493, 768, 788, 35, 105, 655, -220, 0, 170, 443, -1013, -289,
  118, -301, 461, -352, -1111, -959, -1067, 0, -111, -38, 815, 52, -24, -56,
  -854, -320, 446, 579, 440, -62, -212, -674, 370, 400, 145, 525, 95, -219,
  242, -1201, -240, -27, -76, 0, -428, -77, 1141, 368, -124, -947, 576, 546,
  -522, -45, -243, 1499, 366, -547, -284, 801, 1077, 84, 292, -1400, -533,
  9, 1040, 1263, 141]

theorem fractionalNearFrameSubtreeG5R0139_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0139Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0139Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0139Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0139_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0139LowerBoundTable : List ℤ :=
  [-368, 420, 624, 1434, 32, 32, 2199, -1051, -75, 109, 2910, -1361, -1729,
  2654, 690, -1219, 98, 1193, 100, 3400, 78, 1783, 1100, 2096, 2942]

def fractionalNearFrameSubtreeG5R0139LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0139Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0139LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
