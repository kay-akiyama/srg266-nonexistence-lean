import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0193`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0193Mask : ℕ := 6867191218449064

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0193Witness : Array ℤ :=
  #[-536, -25, -350, 85, 194, 5, 442, 5, 739, 437, -381, -665, -319, -204,
  -144, 396, -91, 302, -118, -346, 270, -273, -464, 669, -520, -249, 45,
  333, 34, -639, -342, 546, -5, 0, -266, 707, 862, 256, 219, 246, -108, 150,
  179, -133, -648, 968, 201, 452, 125, -394, -973, -199, -859, -510, 579,
  -402, 18, 62, 112, 855, 858, -27, 291, -101, -38, 555, -620, 511, 329,
  -691, 221, -154, -169, -565, 147, -397, 435, -301, -47, -27, 109, -407,
  290, -226, -55, -404, 45, 108, -23, -267, 513, 63, 108, -358, 168, -184,
  -221, -138, 546, -173, -424, -145, -5, 252, -65, 212, 38, 260, -379, -428,
  132, -286, -135, 339, 347, 15, 410, 403, 339, 498, -36, -334, -816, -491,
  -155, -574, 378, 411, 164, 256, 594, -130, 536, -425, -29, -63, 923, 161,
  884, 185, 311, -562, 89, -992, -529, -398, -822, -196, 353, -566, 843, 0,
  -576, -652, 230, 172, 237, -10, -16, 830, 246, 134, 660, 443, 668, 234,
  256, -524]

theorem fractionalNearFrameSubtreeG3R0193_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0193Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0193Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0193Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0193_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0193LowerBoundTable : List ℤ :=
  [-206, 365, 182, 32, 31, 31, -100, -278, -173, 2153, 236, -2, 520, 876,
  999, 490, 660, 2087, 2152, -1660, 115, 1604, -10, 722, 101]

def fractionalNearFrameSubtreeG3R0193LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0193Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0193LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
