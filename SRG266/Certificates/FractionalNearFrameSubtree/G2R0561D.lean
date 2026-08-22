import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0561`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0561Mask : ℕ := 6845368991683210

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0561Witness : Array ℤ :=
  #[41, -26, -89, 26, -44, -87, -1, 76, 49, 27, -52, 84, 42, 68, -1, 1, 27,
  -27, -21, 54, -6, 10, 43, 72, 33, -1, -88, 18, -38, -1, 32, -52, -37, 62,
  0, -7, -49, 41, 34, -1, 14, 3, -14, -16, -52, -30, 86, 41, 8, 17, -1, -1,
  -40, 99, -23, 71, -2, 81, -61, 15, -16, 15, -71, -19, 0, -14, -36, 20, -1,
  -17, 83, 34, 129, 75, 9, -58, -41, -56, 9, -9, 51, -50, 29, 1, 26, -17,
  102, -56, 12, 54, -53, -18, 52, 31, 44, -32, -40, -24, 49, 41, 58, 7, -41,
  -53, 119, -14, -14, -17, 39, 46, 64, 55, -37, -2, 27, 30, 51, -49, 14,
  -27, -18, 4, -6, -8, 2, -18, -32, 41, 64, -45, -51, -2, -28, -8, -2, 65,
  31, 37, 68, 1, -12, -1, 26, 17, 19, -26, 22, 36, 13, 18, 6, 107, 0, 45,
  -59, 67, -19, 5, -16, -15, -27, -17, -69, -52, -57, 46, -7, -1]

theorem fractionalNearFrameSubtreeG2R0561_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0561Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0561Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0561Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0561_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0561LowerBoundTable : List ℤ :=
  [19, 21, 18, 116, 110, 1, 163, 31, 124, 232, 162, -84, 120, 220, 83, -7,
  103, 302, 161, 219, -118, -102, 138, -94, 201]

def fractionalNearFrameSubtreeG2R0561LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0561Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0561LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
