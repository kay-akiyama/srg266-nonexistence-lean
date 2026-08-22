import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0113`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0113Mask : ℕ := 1309975461740625

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0113Witness : Array ℤ :=
  #[-87, -139, -71, -114, -104, -69, 0, 81, 72, 44, 65, 87, 69, 127, 31, 66,
  0, 48, 66, 23, 25, 41, 38, -17, 33, 85, 46, 48, -50, -52, -1, 48, 74, 64,
  33, 89, 64, -32, -76, -13, -45, 16, -16, 8, 0, -9, -64, 13, 38, 21, 116,
  -35, 3, 6, -17, -57, 5, 25, -18, 41, 20, -19, 16, 15, 21, 5, -20, 10, 40,
  -26, -12, 2, 4, -2, -26, -1, 6, 52, -41, 7, 7, 17, -26, 12, 25, -70, 42,
  20, -11, -2, 41, 25, 15, 0, 23, 97, 0, 30, 49, -26, 47, 31, -85, 39, 46,
  -26, -26, -65, -3, -84, -63, -3, 73, -42, 10, 195, -11, 4, 0, -3, 19, 53,
  34, -29, -14, -35, -7, -11, -12, 15, -4, -5, -12, 7, 20, 19, 32, 8, 14,
  -49, 10, 31, 31, 37, 15, 0, 38, 34, 21, 37, 3, 80, 14, -28, -14, -15, -8,
  27, 2, -4, -9, -41, 13, -19, 53, 109, 47, -104]

theorem fractionalNearFrameSubtreeG2R0113_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0113Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0113Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0113Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0113_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0113LowerBoundTable : List ℤ :=
  [77, 126, 73, 50, 2, 185, 92, 1, 166, 275, 130, 143, 126, 4, 91, 119, 262,
  10, 139, 28, 363, 97, 44, 148, 208]

def fractionalNearFrameSubtreeG2R0113LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0113Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0113LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
