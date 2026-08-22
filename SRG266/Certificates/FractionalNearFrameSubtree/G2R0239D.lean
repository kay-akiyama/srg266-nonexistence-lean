import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0239`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0239Mask : ℕ := 5108179298669073

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0239Witness : Array ℤ :=
  #[0, -539, -196, -548, -94, 0, 852, 1037, 706, 754, 872, 512, 0, -656,
  296, 496, -671, -583, -135, -181, -257, 116, -425, 1047, 678, -15, -237,
  -316, 367, 97, 64, -98, 70, 30, 175, 675, -75, 411, -376, -754, 412, 505,
  312, -34, -224, -503, 120, 318, 0, 256, 309, -26, -24, 289, 328, 310,
  -735, -209, 249, -37, 127, 524, 81, -213, 353, 357, 363, -634, -28, -493,
  -22, -234, -128, 210, 396, 603, 7, 24, -301, 387, 152, -748, 13, -113,
  -295, -763, -413, -332, -160, -281, -142, -273, -516, 85, 305, 249, 336,
  86, -392, 307, 796, 541, 240, 956, 54, -508, 70, 571, 1473, -1295, -446,
  -571, -1308, 7, 1933, 751, -141, 820, 938, -224, -1014, -446, -573, 43,
  -164, 728, 104, 417, 538, 443, -610, 225, 43, 638, 327, 379, -531, -333,
  405, 151, -722, 336, 113, -380, 896, 929, 1037, 593, 762, -327, 607, -162,
  87, -19, -172, -324, -1008, 251, -710, -1241, 89, 640, -520, 255, 859,
  745, 207, 251]

theorem fractionalNearFrameSubtreeG2R0239_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0239Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0239Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0239Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0239_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0239LowerBoundTable : List ℤ :=
  [623, 1346, 655, -738, 1038, 2534, 604, 2250, 619, 3612, 628, 2658, 99,
  1790, 797, 1531, 171, -1516, -324, -1302, -472, -179, 899, 678, 1780]

def fractionalNearFrameSubtreeG2R0239LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0239Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0239LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
