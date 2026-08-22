import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0078`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0078Mask : ℕ := 5438859118224646

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0078Witness : Array ℤ :=
  #[96, 77, 145, 9, 41, 69, 76, 151, 119, 80, 106, -108, 0, -25, -195, -72,
  -393, -167, -113, -287, -183, 165, 25, 192, 166, 108, 192, 209, 98, 129,
  352, 235, 13, 17, -61, 112, 110, -117, 112, 39, 125, -12, 138, -30, -49,
  62, 43, 42, -112, -9, 135, -82, -77, 89, 53, 164, 126, -16, 56, 56, 99,
  -96, -129, 155, 140, -320, 47, 37, 18, -383, -96, 96, -65, 63, 59, 167,
  81, -48, -120, -148, 120, 123, -55, 195, -20, -17, -51, 39, 45, 39, 199,
  109, -98, -70, -101, 182, 116, -40, 87, -61, 163, -7, -86, 126, 24, -53,
  -82, 125, 118, -139, -39, 209, 158, 24, -1, 3, -14, -19, 196, -71, 301,
  16, -104, -83, -81, 7, -51, 99, 89, -62, 16, 58, 270, -236, 34, -6, 287,
  -201, 211, 29, -130, 157, 34, 150, 80, -26, -130, 107, -179, 56, 84, 52,
  44, -208, 106, -5, 78, -213, -96, -225, -21, 73, 32, 84, 23, -104, -473,
  191]

theorem fractionalNearFrameSubtreeG5R0078_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0078Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0078Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0078Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0078_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0078LowerBoundTable : List ℤ :=
  [99, 49, 2, 391, -20, 194, 402, 420, 390, 11, 163, 720, 278, 231, -121,
  390, 636, 349, 9, 675, 25, 10, 10, 477, 440]

def fractionalNearFrameSubtreeG5R0078LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0078Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0078LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
