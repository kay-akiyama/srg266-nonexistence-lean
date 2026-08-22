import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0486`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0486Mask : ℕ := 5811138987672140

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0486Witness : Array ℤ :=
  #[135, 861, 791, 1118, 1158, -44, -78, -237, 492, 260, 641, -1590, -1279,
  -534, -1499, -541, -652, -522, -499, -89, -443, -170, -527, 37, -493, 681,
  347, 810, 777, 660, -128, 7, 426, 331, 112, 270, -295, -23, 587, -117,
  -106, 556, 178, -441, -218, 23, 451, 22, -431, 96, 65, 148, 438, -175,
  900, 935, -388, -228, 112, 20, -94, 0, 449, -145, 118, 75, 306, 202, -5,
  345, 37, -340, -244, 917, -486, 59, 270, 41, -272, 122, 262, -525, -127,
  184, 366, -256, -1, -469, -469, -187, -285, 65, 47, -392, 172, -364, 108,
  -209, -384, -449, -133, 446, 490, 52, 146, -141, -88, 769, 717, 279, 551,
  -306, 471, 404, -175, 711, -81, 414, 256, 140, 470, 552, 290, 535, -263,
  75, 1047, 342, -89, -234, -674, -516, -466, 639, 894, 433, -133, 7, 350,
  -142, -547, -682, -720, -325, -522, 23, 379, -140, 293, 153, 641, -142,
  -402, -30, 1205, 272, 238, 226, -452, 470, 89, 467, 499, 923, 711, 547,
  -351, 192]

theorem fractionalNearFrameSubtreeG2R0486_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0486Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0486Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0486Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0486_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0486LowerBoundTable : List ℤ :=
  [659, 1430, 1984, 31, 927, 33, 1371, 317, 32, 2311, 2300, 1540, 1855,
  3024, 2468, 99, 1836, 1284, -1033, 812, -1078, 611, 1703, 954, 98]

def fractionalNearFrameSubtreeG2R0486LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0486Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0486LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
