import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0007`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0007Mask : ℕ := 798025882470659

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0007Witness : Array ℤ :=
  #[19, 22, -41, 48, 8, 64, 20, -66, 65, 30, 127, 0, 110, -78, -45, -66, 46,
  -41, 52, -73, 34, 36, -8, -60, -44, 58, 73, 102, 30, 0, -12, -37, 41, 41,
  45, 49, 30, 40, 23, 13, -72, -13, 41, -43, 60, 50, 48, 84, -9, 16, 4, -19,
  4, -46, -72, -11, 11, 23, 24, 84, 3, -34, 70, 51, 36, -48, -40, 10, 98, 5,
  -20, 30, -11, -26, -13, 89, -13, 10, 84, 42, 34, 9, 33, 112, 25, 24, 37,
  25, 65, 25, -7, 56, -69, 36, 67, 23, -3, 22, 17, -28, -17, 13, 18, 35,
  -67, -104, 36, 33, -10, -27, 34, 26, -63, -25, 42, -20, -77, -22, 82, 17,
  5, -10, -4, 3, -117, -49, 133, -57, 31, -16, -12, -9, -2, 5, 2, -19, 92,
  68, -44, -21, 31, -58, -39, -30, -39, -73, -23, 73, 68, 88, -98, -5, -80,
  -102, -45, -67, -40, 18, -22, -39, -17, -96, 18, 120, 78, 54, 0, 111]

theorem fractionalNearFrameSubtreeG5R0007_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0007Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0007Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0007Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0007_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0007LowerBoundTable : List ℤ :=
  [55, -81, 44, 131, 171, 238, 148, -38, 78, 196, 13, -182, 10, 147, 289,
  10, 76, 279, 10, 11, 171, 10, 653, 192, 27]

def fractionalNearFrameSubtreeG5R0007LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0007Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0007LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
