import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0065`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0065Mask : ℕ := 954133598814610

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0065Witness : Array ℤ :=
  #[76, -430, 65, 514, -167, 223, -257, 26, 40, -130, -401, 229, 189, 322,
  -169, 646, 225, -461, 130, 281, -308, -2, -189, 408, 347, -21, 135, -281,
  24, 105, 38, 822, 277, 59, 609, -137, -360, -144, -147, -183, -53, -366,
  7, 144, 153, -476, 601, 29, 140, 691, -578, -2, -310, -376, 327, -148, 86,
  352, 305, -609, -22, -343, -354, 180, 256, 343, 362, 213, -41, 354, -176,
  -214, -207, 40, -224, -183, 119, -243, -47, 424, -272, -14, 360, -34, 133,
  -214, -411, 354, -623, 43, 269, -194, -388, 461, -800, -368, -166, -308,
  302, 191, 318, -190, -161, -77, 37, 18, 194, -238, -461, -98, 180, -331,
  15, 288, 165, -80, -585, -199, -156, 222, 443, -498, 195, 114, -292, -160,
  -248, -372, -1163, 746, 482, 5, 37, 655, 356, -38, -232, -27, -134, 32,
  -161, 607, -333, -163, 284, -274, -186, 46, 277, 262, -682, 339, -262,
  -364, 403, -122, 367, 100, 297, -420, 355, -443, 99, 354, -271, 238, 2,
  200]

theorem fractionalNearFrameSubtreeG2R0065_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0065Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0065Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0065Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0065_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0065LowerBoundTable : List ℤ :=
  [-544, -172, 31, 32, -276, 31, 436, 32, 30, 90, 2248, -670, 336, -253,
  464, 100, 101, -527, 1175, -526, 2009, 100, -84, -257, -1200]

def fractionalNearFrameSubtreeG2R0065LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0065Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0065LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
