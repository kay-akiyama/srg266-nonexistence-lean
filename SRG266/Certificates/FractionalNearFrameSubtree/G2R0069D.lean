import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0069`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0069Mask : ℕ := 957283544432866

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0069Witness : Array ℤ :=
  #[-13, 33, 6, 85, 18, 29, 214, 47, 110, -19, 89, 46, -114, -9, -141, -98,
  49, -127, -3, -59, 112, 127, -13, 17, 56, -87, 77, -5, 100, 72, 119, 62,
  162, 27, 30, 201, 134, -65, -107, 142, -15, -89, -149, -170, -185, -25,
  -170, 63, -7, 122, 102, 232, -34, -37, -41, 115, 103, -5, -110, 2, -46,
  -42, -20, 14, 62, -38, 44, 42, 18, -67, 58, 16, -17, -35, -8, -119, 10,
  47, -93, -37, -33, -30, 70, -35, -98, -1, 57, -70, 71, 5, -55, 18, -28,
  -84, 86, 135, -137, 34, 69, 1, -10, -70, 56, -82, 27, 169, 60, -45, 91,
  35, -57, 4, -69, 0, -12, 45, -29, 13, 36, 70, 51, 89, 73, 5, 3, 105, -32,
  -21, -82, 56, -79, 59, 10, 56, 8, -55, -39, -74, 3, 86, 5, -67, 108, 71,
  66, 91, 40, 95, -19, -89, 27, 59, -38, 183, -9, -55, -51, -87, 81, -58,
  -164, -49, 80, 43, -4, 36, 73, -102]

theorem fractionalNearFrameSubtreeG2R0069_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0069Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0069Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0069Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0069_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0069LowerBoundTable : List ℤ :=
  [22, 183, -168, -35, 37, 351, 77, 66, 313, 408, 171, 36, 65, -8, 28, -215,
  26, -90, 262, 10, 49, 623, 10, 256, 511]

def fractionalNearFrameSubtreeG2R0069LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0069Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0069LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
