import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0079`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0079Mask : ℕ := 971456795058408

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0079Witness : Array ℤ :=
  #[35, 69, 25, 94, 45, -12, -7, -11, 28, -16, -11, -10, -23, -5, -28, 10,
  -65, -62, -50, 38, 76, 51, -35, 17, 47, 33, 7, 12, 26, 40, -34, -14, 48,
  42, -11, 30, 27, -19, -18, 71, 0, 0, -6, 1, -10, 58, 61, -9, 44, -1, -92,
  -66, 85, -38, 17, 16, 45, -111, 3, -11, -75, -76, 76, 0, 32, 63, 72, -34,
  -49, 2, -46, 16, 15, 123, 0, -21, 56, -48, -28, 42, -68, -78, -5, -4, -75,
  -35, 119, -84, -20, 107, 16, 11, -26, 48, -20, 14, 29, 15, 53, 34, 4, -9,
  -67, -41, -4, 21, 109, -24, 22, 69, 43, -20, 21, 6, -112, 17, 4, 52, 53,
  41, 49, 80, 37, -120, 36, 87, 20, -37, 26, -21, -15, -5, 134, 65, -123, 6,
  22, -10, 23, -52, 70, 42, -6, 59, -54, -110, -1, 51, 9, -33, -13, 25, -4,
  -97, 59, 26, -6, -15, -62, 86, -47, -22, -55, 65, 99, 13, 12, 46]

theorem fractionalNearFrameSubtreeG2R0079_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0079Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0079Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0079Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0079_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0079LowerBoundTable : List ℤ :=
  [4, 152, 97, 5, -8, 119, 4, -32, 143, 304, -9, 206, -107, -34, 97, 10,
  291, 196, 81, 183, 333, 126, 213, 10, 165]

def fractionalNearFrameSubtreeG2R0079LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0079Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0079LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
