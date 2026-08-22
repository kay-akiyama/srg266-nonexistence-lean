import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0305`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0305Mask : ℕ := 5387246958781528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0305Witness : Array ℤ :=
  #[-15, 55, 108, 95, 25, -234, -12, 169, 106, -41, 6, -173, -11, -22, -241,
  45, -66, 15, 40, -18, 131, -34, 47, 36, 194, 38, 122, 174, 37, -55, -19,
  155, 0, -335, 78, 287, 147, -94, -153, -28, 500, 165, 229, -56, 172, 180,
  -70, 40, -229, 160, -15, -149, 30, -109, 17, 36, 135, 0, -185, 101, -57,
  84, -51, -71, 96, 17, 117, 214, -91, 199, 127, 57, 14, 7, 120, 65, 131,
  -16, 95, -16, 129, -20, 34, 32, 123, 58, 217, 15, -161, 212, -20, 107,
  125, 18, 99, 5, 7, 201, 66, -23, -267, 60, -31, 186, -106, -77, 8, -166,
  -72, 267, 220, 240, 143, -153, 331, -78, 164, 86, -96, 88, -70, 15, 103,
  41, -109, -251, -178, 213, 61, -349, 27, -265, 76, -8, 211, -7, -44, -125,
  -100, 201, -4, 40, 2, -242, 182, 119, 102, 75, -203, -21, 110, -130, 122,
  78, 115, 97, 29, 40, 80, 238, 9, 62, 36, -184, 119, 70, 0, -185]

theorem fractionalNearFrameSubtreeG2R0305_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0305Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0305Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0305Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0305_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0305LowerBoundTable : List ℤ :=
  [244, 208, 513, 283, 144, 404, 518, 321, 142, 526, 258, 523, 9, 5, 587,
  732, 109, 565, 597, 570, 302, 848, -120, 362, 170]

def fractionalNearFrameSubtreeG2R0305LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0305Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0305LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
