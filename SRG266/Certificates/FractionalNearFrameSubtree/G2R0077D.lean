import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0077`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0077Mask : ℕ := 971439749927144

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0077Witness : Array ℤ :=
  #[46, 77, 47, 41, -86, 36, 13, -23, 21, 6, 16, 68, -89, -25, 127, -21, 10,
  -4, -36, 58, -32, -49, -28, -67, 45, -2, -3, 134, 34, -68, 53, -37, 86,
  -71, -68, 89, 73, -48, 82, -40, -166, -91, -4, 37, -130, -12, 86, 86, 63,
  -74, -131, -24, 95, -89, 9, 7, -88, 62, 73, 72, -28, -39, 41, -6, 49, -51,
  -18, 2, 64, 57, -70, 118, 19, 68, 115, -20, 105, 32, 42, -59, 6, -64, 18,
  -25, 51, 5, 21, 63, 114, -2, 20, 35, 48, -13, -56, 47, 66, 21, 98, 41, 28,
  89, 11, 166, 82, -49, -63, 59, -56, -31, -30, 88, 4, -119, -44, -5, -30,
  5, 17, -34, -36, 40, 8, 116, 37, 48, 4, 117, -42, 28, 35, 32, 25, 45, -18,
  5, 39, 67, 4, 79, -17, 2, 81, -9, 72, -3, -26, -24, -125, 132, 10, -33,
  -17, 54, 32, 41, 43, 92, -81, 83, -11, 97, -38, 136, 122, 95, 39, -15]

theorem fractionalNearFrameSubtreeG2R0077_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0077Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0077Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0077Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0077_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0077LowerBoundTable : List ℤ :=
  [142, 302, 151, 345, 34, 173, -35, 74, 232, 340, 10, 15, 74, 197, 178, 9,
  286, 687, 222, 242, 341, 11, 377, 264, 246]

def fractionalNearFrameSubtreeG2R0077LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0077Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0077LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
