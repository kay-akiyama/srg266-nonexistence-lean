import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0353`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0353Mask : ℕ := 5671090799614497

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0353Witness : Array ℤ :=
  #[-3, 441, 427, 270, 496, 337, -102, 144, 83, 229, -116, 288, -663, -573,
  -462, -294, -502, -137, -248, -167, -164, -216, -158, 7, -246, -84, -81,
  -11, 490, 367, 361, 566, -325, -124, 80, -30, 189, 49, 35, 243, 0, -189,
  185, 21, 434, -65, -233, 306, 47, 288, 142, 489, -13, -12, -8, 17, -33,
  -8, -15, -146, -200, 343, 122, -70, 41, -10, 276, -178, -23, -281, -19,
  141, 224, 196, 104, -123, -55, 229, 148, -79, 144, 107, -15, 54, -73, -40,
  73, -132, -97, 59, 22, -4, 103, -187, 149, -44, -59, 129, 43, -81, 127,
  203, 153, 328, 149, 37, 67, -2, 163, 318, 0, 165, 60, -254, -42, 285, -5,
  -104, 54, 172, 234, 91, -33, 70, 10, -202, -48, 311, -94, -105, 157, 63,
  -204, 161, -142, 78, -141, -55, -22, 133, -62, -182, -107, 209, -97, 89,
  -273, 173, -71, 121, 160, -94, -71, 290, 48, -53, 285, 53, -74, 373, 11,
  201, 132, 181, -94, 111, 232, 120]

theorem fractionalNearFrameSubtreeG2R0353_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0353Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0353Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0353Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0353_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0353LowerBoundTable : List ℤ :=
  [251, 417, 506, 429, 668, 190, 2, 282, 359, 9, -141, 1135, 1071, 634, 431,
  106, 588, 11, 475, 1511, 524, 137, 1813, 773, 695]

def fractionalNearFrameSubtreeG2R0353LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0353Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0353LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
