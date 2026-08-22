import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0468`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0468Mask : ℕ := 5808416757818514

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0468Witness : Array ℤ :=
  #[-96, -111, 52, 83, 20, -40, 20, 124, 73, 152, 19, 35, 0, -17, 88, 89,
  -40, -83, 115, 155, 11, 129, 181, 87, 142, 67, 32, -138, 0, 157, -98, 91,
  -59, 156, 84, 69, 95, 92, 52, 43, 90, -35, 0, 37, 169, 2, 82, 182, -161,
  69, 22, 150, 86, -79, 66, 159, 48, 30, 180, 219, 138, -69, 1, -11, -49,
  -28, 85, 57, 158, 187, -54, -38, 43, -9, 106, -3, 134, 105, -155, 121, 7,
  -60, -31, 10, 239, -113, -174, 140, 91, 92, 13, 4, -106, 89, 94, 9, -125,
  32, 127, 139, -104, -196, 283, 20, 123, 49, 54, -253, -132, -345, 50, 37,
  30, 14, -28, 166, 99, -136, 23, -32, -21, 113, 3, -238, 65, -220, -193,
  -128, -162, -67, 263, -145, 43, -131, 10, 150, -109, 137, 52, 106, 173,
  126, 190, 2, 156, 17, 437, -22, -70, 95, 42, -97, 176, 130, 23, 63, -91,
  1, 6, -171, 39, -59, -70, -117, -20, 56, -24, 39]

theorem fractionalNearFrameSubtreeG2R0468_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0468Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0468Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0468Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0468_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0468LowerBoundTable : List ℤ :=
  [227, 20, 117, 742, 278, 213, 420, 218, 593, 181, 213, 423, 91, 273, 204,
  10, -119, 497, 1036, 112, 1082, 261, 955, 372, 10]

def fractionalNearFrameSubtreeG2R0468LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0468Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0468LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
