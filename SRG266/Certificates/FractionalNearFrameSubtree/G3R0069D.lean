import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0069`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0069Mask : ℕ := 1041350962877012

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0069Witness : Array ℤ :=
  #[28, 33, -58, 84, 10, 114, 43, -14, 3, -57, 1, 10, 0, -9, -130, 45, -13,
  -44, 20, 36, 134, 38, 61, -39, -52, -39, 158, -51, -153, -6, 35, 55, -29,
  -15, 54, -2, -26, 116, 30, 55, 81, 8, -78, -126, 15, 39, 51, -28, 17, 48,
  0, 37, 53, 65, 12, -80, -107, 34, 6, -52, 37, -20, -13, 43, -64, 70, 51,
  -27, 68, 9, 21, -104, -112, 45, -9, -82, 54, 133, 47, -11, 42, -106, 14,
  -98, -154, 36, 0, 226, 44, 97, -18, 35, 38, -263, -86, 119, 99, 112, -20,
  28, 60, -119, -44, -17, -41, 61, 4, 34, 92, 32, 89, 62, -62, -149, -191,
  -87, -141, -100, 85, -92, 17, 152, -33, -12, -52, 100, 29, -34, 13, -45,
  -2, -23, 23, -29, -49, -2, -42, -68, 62, 22, -1, 71, -49, 13, 103, -17,
  -52, 22, -41, -70, 39, -87, 63, -11, 139, 196, 231, 1, -39, -65, 12, 166,
  -14, 124, 5, 40, -143, 84]

theorem fractionalNearFrameSubtreeG3R0069_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0069Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0069Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0069Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0069_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0069LowerBoundTable : List ℤ :=
  [-29, 67, 64, 2, 57, 47, 90, 147, 2, -86, 23, 131, 185, -137, 9, 8, 186,
  146, 167, 271, -306, 491, 320, 27, 217]

def fractionalNearFrameSubtreeG3R0069LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0069Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0069LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
