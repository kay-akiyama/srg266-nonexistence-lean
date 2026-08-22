import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0413`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0413Mask : ℕ := 5746706787021976

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0413Witness : Array ℤ :=
  #[690, 215, -112, 11, 314, 341, -305, -217, 117, -90, -25, 258, -519, 320,
  813, 238, 188, 81, 238, 488, 218, -214, 170, -592, 44, 823, -283, -285,
  109, 143, 349, 561, -246, 357, 913, -301, -308, -676, -275, 245, -53,
  -327, -725, 471, -274, 796, -335, 807, -609, -299, -424, -20, 419, 1176,
  -920, 43, -229, 235, -265, -277, -69, -715, 815, 683, 589, -349, -34,
  -503, -64, -27, -143, -47, -41, 489, 942, 60, -434, 91, 435, 1050, -27,
  309, 551, -2, 676, 872, -800, -346, -34, -404, -108, -86, 269, 157, 686,
  60, -114, 355, -894, 72, -723, -242, -205, 278, 721, 554, 487, 702, 249,
  -157, 233, -985, -517, 66, -21, -521, 0, -531, 59, 800, 517, -236, -349,
  1024, -174, -77, 468, 411, 102, 170, -93, -20, 705, -1009, -762, 106, 842,
  -530, 483, 380, 404, 811, -450, 1408, -531, 1131, -591, 862, -910, 400,
  420, -619, 716, -201, -1145, -1016, -234, 696, 220, 98, -368, -250, 245,
  -306, -704, -207, -167, -133]

theorem fractionalNearFrameSubtreeG2R0413_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0413Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0413Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0413Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0413_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0413LowerBoundTable : List ℤ :=
  [-30, -156, 32, 973, 1038, 196, 1106, -19, 967, 925, 2811, -749, 236, 317,
  100, 419, -835, 101, 578, 3356, 1291, 2101, 3623, 1820, 223]

def fractionalNearFrameSubtreeG2R0413LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0413Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0413LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
