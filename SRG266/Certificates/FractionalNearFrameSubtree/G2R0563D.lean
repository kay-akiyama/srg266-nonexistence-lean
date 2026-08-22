import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0563`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0563Mask : ℕ := 6846331064328842

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0563Witness : Array ℤ :=
  #[-31, 95, -2, -41, -78, 120, -60, 47, -31, 0, -84, 82, -32, -41, 152,
  267, 109, -28, -113, 6, 0, 109, 228, 104, 3, 36, 35, -94, -182, -128, 57,
  21, -44, 75, 28, -127, -152, 79, 119, 68, -47, -99, -42, -111, 14, -49, 6,
  14, 30, -82, -27, 14, 8, 83, -176, 92, -33, 105, -94, 138, 0, -99, 143,
  -79, 154, 120, -99, -109, -48, -14, 12, 156, 41, -116, 128, 55, -11, -127,
  3, -8, -39, 60, -15, -7, 53, 111, 20, -50, -43, -35, -62, -74, 258, 207,
  -79, 15, 29, -50, -71, 100, -79, 86, -91, 171, -39, 70, -84, 36, 131,
  -238, 59, -40, 92, -94, -126, -62, 189, 0, 121, 77, 31, -127, -12, 90,
  126, 51, -207, -38, -26, -13, 115, 105, -34, -219, -76, -24, -19, 168,
  -40, -39, -62, -65, -159, 170, 324, 241, 103, 63, 83, 29, -67, -167, 24,
  51, -76, -27, -119, 115, 213, -153, -16, 22, -50, -28, 40, 104, 55, -100]

theorem fractionalNearFrameSubtreeG2R0563_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0563Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0563Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0563Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0563_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0563LowerBoundTable : List ℤ :=
  [-56, 170, 44, 151, -118, 23, 216, 74, 50, -473, -187, 833, 141, 10, 860,
  498, -181, -98, -161, 352, -339, -403, 472, 467, 605]

def fractionalNearFrameSubtreeG2R0563LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0563Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0563LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
