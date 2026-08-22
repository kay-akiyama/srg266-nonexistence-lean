import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0142`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0142Mask : ℕ := 6879874860919817

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0142Witness : Array ℤ :=
  #[-27, -105, -60, 44, 37, 75, 0, 97, -38, -2, 69, 68, -44, -36, -9, 41,
  -25, -32, -82, -21, 19, 86, 52, 39, 116, -3, 38, 70, 0, 70, -23, -44, -27,
  -85, -96, -76, 10, 5, 107, 54, 145, 30, -14, -41, 77, 47, 34, 91, -13, -3,
  40, -17, -29, 51, 36, -101, 86, 45, 15, -91, 29, -62, 96, 26, -74, 82, 86,
  43, -62, -33, 73, 45, 39, -94, 21, -76, 0, 45, -72, -14, 10, 12, -8, -79,
  29, -15, -37, -56, 33, 29, 15, 26, 31, 74, -96, 19, -72, 41, 69, 56, -47,
  -88, -13, -13, 3, -26, -13, -93, -49, 72, 23, 4, -51, 89, 24, 78, -9, -36,
  32, 13, -64, -11, -13, 12, -26, -31, 19, -3, 24, -58, -101, -20, -108, -1,
  -69, -46, 10, 66, 38, 35, -1, -77, -57, -61, 39, -6, 39, -48, 77, -87, 55,
  -45, 90, -5, -68, 29, 0, -16, -8, 8, 40, 91, 21, 80, 62, 37, 24, 43]

theorem fractionalNearFrameSubtreeG5R0142_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0142Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0142Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0142Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0142_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0142LowerBoundTable : List ℤ :=
  [-48, 28, 1, 2, 21, 122, 2, 132, 2, 227, 10, -266, -3, 320, -158, -28,
  263, 183, 187, 168, 97, 10, 28, 427, -118]

def fractionalNearFrameSubtreeG5R0142LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0142Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0142LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
