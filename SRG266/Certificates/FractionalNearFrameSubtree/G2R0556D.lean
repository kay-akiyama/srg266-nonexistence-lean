import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0556`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0556Mask : ℕ := 6841802264515668

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0556Witness : Array ℤ :=
  #[-78, -34, -15, -14, 64, 33, -19, 40, 10, 27, -18, -89, 40, -111, 70, 66,
  -9, 15, -49, 45, -36, 6, 6, 15, 5, 22, 1, -39, 40, -35, 30, -60, 41, 111,
  -199, -174, 148, 96, 183, -106, -100, -115, 48, 180, 60, 40, -32, -40, 6,
  -80, -127, -38, 86, 50, 85, 26, -104, 32, 6, -35, 69, 82, 15, 53, 13, 34,
  57, 64, -25, -28, -34, -37, -54, -3, -32, 62, -67, 75, 74, 32, -40, 14,
  41, 26, 26, -44, -22, 57, 3, 136, 72, -2, 0, 84, 21, 28, 4, 34, 1, -19,
  38, -56, 1, -62, -85, 23, 116, 62, 0, -46, 46, -17, 11, 96, -40, 50, 28,
  -33, -7, -50, -2, 63, 46, 9, 52, 32, -17, 4, 23, 0, -25, 53, 33, -59, -28,
  12, -40, -46, -56, -13, -44, -52, 35, 41, 33, 47, 50, 107, 38, -8, 68, 35,
  34, 13, -49, -24, 15, -8, 21, -60, 74, -22, 39, -29, 25, -98, -71, -96]

theorem fractionalNearFrameSubtreeG2R0556_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0556Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0556Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0556Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0556_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0556LowerBoundTable : List ℤ :=
  [29, 65, 134, 112, 103, 177, 3, 2, -63, 30, 65, 6, 145, 118, 184, 91,
  -211, 9, 185, 225, 41, 14, 166, 226, 159]

def fractionalNearFrameSubtreeG2R0556LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0556Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0556LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
