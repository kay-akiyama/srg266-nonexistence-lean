import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0046`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0046Mask : ℕ := 931066403209618

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0046Witness : Array ℤ :=
  #[-36, 0, 9, -163, -10, -186, 329, 260, 236, 435, 285, -141, -106, -363,
  -241, -87, 69, -91, -2, -86, -192, -2, 11, -66, -54, -24, 42, 105, 53,
  120, -176, -183, -210, 67, 162, 122, 44, 105, -212, -69, 146, 128, -114,
  -115, -369, -1, -14, 283, 251, 81, 69, -162, -102, -46, 198, 179, 86, -70,
  138, -96, 145, 64, -37, -35, -153, -32, 209, -7, -4, 12, 28, -13, 60, -42,
  76, -65, -97, -90, -8, 8, -92, 92, 68, 112, 134, 9, 248, 36, 18, 104, 1,
  18, 17, 47, 52, -73, 44, 59, -59, 113, 115, -27, 0, 234, 176, 41, 98, 113,
  108, 49, 143, 209, -9, -150, -45, 75, 131, 27, 85, 21, -131, -7, -167, 75,
  25, 140, 71, -96, 0, -75, 11, 26, 31, -105, 10, 2, 97, 228, 47, -67, -91,
  221, -15, -121, -118, -120, -222, -135, 227, -47, 4, -90, -76, -170, 124,
  17, 91, -20, -18, -14, 117, 91, 117, 79, 88, 186, 207, 123]

theorem fractionalNearFrameSubtreeG2R0046_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0046Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0046Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0046Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0046_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0046LowerBoundTable : List ℤ :=
  [78, 147, 344, 49, -182, 260, 156, 372, 207, 296, 239, 529, 824, 193, 310,
  9, 809, -38, 400, 628, -280, 144, 579, 9, 673]

def fractionalNearFrameSubtreeG2R0046LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0046Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0046LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
