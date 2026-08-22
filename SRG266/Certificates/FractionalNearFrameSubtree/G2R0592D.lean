import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0592`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0592Mask : ℕ := 6864960723291224

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0592Witness : Array ℤ :=
  #[-55, -139, -86, 88, 36, 69, -109, -45, 65, -48, 51, 184, 314, 136, 133,
  92, -94, 116, 71, 67, 106, 25, -13, -15, -58, -77, -92, -125, 128, 36, 17,
  57, -158, 42, 103, 55, 52, -50, -83, 0, 13, -63, -168, 59, -68, -85, 61,
  86, 147, 113, -17, -17, -13, 161, -153, -94, 265, 25, -8, -17, 130, -46,
  2, 237, 187, -196, 300, 111, 154, -60, 24, -40, 98, -37, -96, -141, 6, 73,
  29, 24, -38, 54, 45, -109, -97, 38, 104, -63, -2, 116, 57, 57, 143, 36,
  32, 255, -15, -73, 76, 99, 15, -108, 1, -116, 181, 127, 68, 84, -52, -3,
  -90, -70, -85, -30, -49, 125, 177, -28, -61, -1, 268, 32, -41, 77, -106,
  0, 56, -114, 101, -91, -167, -149, -25, 142, 107, 186, -51, 30, -55, -6,
  -41, 73, -131, -16, 61, -153, 231, 70, 59, 74, -109, -62, 198, 277, -62,
  35, 176, -63, -16, 61, -36, 52, 132, -24, 8, -53, -144, -88]

theorem fractionalNearFrameSubtreeG2R0592_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0592Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0592Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0592Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0592_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0592LowerBoundTable : List ℤ :=
  [208, 56, 199, 273, 86, 268, 164, 165, 437, 1009, 205, 8, 54, 224, -137,
  84, 334, 162, 324, 425, 371, 298, 441, 546, 152]

def fractionalNearFrameSubtreeG2R0592LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0592Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0592LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
