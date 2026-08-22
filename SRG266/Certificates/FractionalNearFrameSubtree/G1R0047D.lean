import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0047`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0047Mask : ℕ := 538518580933780

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0047Witness : Array ℤ :=
  #[-24, 0, 44, -48, -127, 9, -6, 80, 25, 7, 46, 105, 88, 56, -73, 100, 37,
  14, 42, 10, 24, 79, -4, 58, 11, -49, -43, 3, -105, -91, -136, -202, 79,
  -56, 17, 57, 28, 26, 29, 71, 127, 173, 110, -27, 50, 44, 92, -8, -107,
  -47, -98, 47, 5, 15, -33, -116, -16, 65, 98, 12, 47, -19, 65, 128, 56,
  -85, 41, -20, 44, 37, 81, 3, -17, -6, -98, 37, 22, 57, -67, 94, -50, 1,
  -25, 22, 51, 50, 42, 32, 14, 87, -22, 84, -9, 25, -13, -45, 62, 29, 52,
  74, 73, 41, 79, 13, 7, 122, 111, 97, -9, -2, 2, 19, -13, 132, 14, -95,
  -88, 10, 57, 40, -73, -73, 18, 46, 67, 63, 2, -123, 12, -58, 127, 46, -85,
  -49, 21, -17, -19, 35, -3, -20, -75, 68, 57, 45, 32, 10, -47, 17, 19, 47,
  45, -85, -21, -32, -84, -7, -73, 36, 8, -7, -117, 73, -26, -20, -35, 8, 4,
  -15]

theorem fractionalNearFrameSubtreeG1R0047_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0047Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0047Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0047Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0047_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0047LowerBoundTable : List ℤ :=
  [70, -29, 78, 279, 9, 160, 110, 161, 107, 182, 12, 109, 11, 202, 362, 281,
  -11, 158, 383, 361, 130, 135, 48, 9, 342]

def fractionalNearFrameSubtreeG1R0047LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0047Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0047LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
