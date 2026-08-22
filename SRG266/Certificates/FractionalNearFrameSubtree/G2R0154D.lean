import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0154`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0154Mask : ℕ := 1378147130884746

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0154Witness : Array ℤ :=
  #[-84, -99, -132, 1, -15, 72, 122, 159, 54, 83, 147, -66, -128, -27, -112,
  7, 31, -12, 124, 6, 1, -26, -151, 40, -18, -79, 77, 177, 36, 24, -28, -39,
  -76, -35, 97, 12, 62, 12, 137, 8, -6, -33, 8, 15, -32, -76, 32, 104, 39,
  69, -32, -7, -56, 86, 12, 91, 79, -32, -19, 20, -58, -141, -126, 77, -6,
  -27, 29, 22, -28, 12, 58, 81, 57, 15, -23, 5, 2, 131, -30, -24, -56, -64,
  85, 35, 9, -46, 59, 52, -51, -26, 114, 83, -73, 41, -2, 10, 58, -2, 15,
  67, 16, -6, -13, -7, 18, 49, -54, 4, 42, 11, 53, 84, -2, -28, 4, -5, 10,
  -48, 65, 91, -85, 74, 86, 43, -46, -34, -33, 52, 4, 54, 40, 48, -72, 76,
  -2, -53, 37, 27, 45, 37, -11, 68, -46, 128, 37, -11, 40, -8, -25, -26, 30,
  81, -48, 5, 8, 13, 75, -23, 43, 33, -69, -36, 45, 34, -22, 81, -43, 53]

theorem fractionalNearFrameSubtreeG2R0154_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0154Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0154Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0154Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0154_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0154LowerBoundTable : List ℤ :=
  [61, 157, 47, 217, 119, 79, 46, 145, 5, 274, 391, 219, 73, 373, -54, -124,
  -87, 231, 417, 636, -80, 340, 531, 108, 182]

def fractionalNearFrameSubtreeG2R0154LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0154Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0154LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
