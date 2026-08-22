import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0113`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0113Mask : ℕ := 5386216733843858

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0113Witness : Array ℤ :=
  #[84, -63, 76, -163, -240, -111, 113, 143, 149, 278, 86, -10, 8, -163, 0,
  -51, 110, -38, -100, 18, -252, 34, -88, 8, -51, 172, 135, 48, -42, 144,
  109, -151, 157, -112, 22, 0, 28, -30, 47, 33, -79, -25, -73, 70, -58, -56,
  38, 12, -45, -102, 21, 108, 101, 169, 7, -62, 30, 0, -243, -80, 160, -48,
  -67, 118, 101, 53, -72, -104, 240, 46, -41, 17, 124, -38, 24, 149, -66,
  22, 272, -27, 46, 62, -48, -6, 16, 37, 257, 80, 226, 113, 112, 46, 192,
  164, 78, 240, 165, 198, 60, 15, 60, -68, 94, 83, 68, 2, 46, 78, 30, -5,
  287, 30, -175, 56, -131, 8, -153, 39, -24, -54, -85, 70, -85, 116, -145,
  127, 58, -29, 162, 175, 84, -56, -129, 145, -33, -30, 69, 17, 46, 48, 141,
  -90, -36, -17, -72, 15, -73, -25, 128, -32, 27, 132, 114, -30, -32, -165,
  -124, 137, -109, 43, -133, -124, -212, -37, -151, -72, 147, -8]

theorem fractionalNearFrameSubtreeG3R0113_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0113Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0113Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0113Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0113_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0113LowerBoundTable : List ℤ :=
  [104, 0, 311, 541, 238, 1, 207, 177, 126, -210, 8, -139, -146, 1069, 619,
  418, 79, 427, 195, 324, 435, 451, 741, 11, 189]

def fractionalNearFrameSubtreeG3R0113LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0113Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0113LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
