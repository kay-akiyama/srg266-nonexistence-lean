import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0038`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0038Mask : ℕ := 954161585422674

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0038Witness : Array ℤ :=
  #[74, 39, -3, -36, -37, 92, 0, -20, 43, 43, 33, -22, -95, -64, 35, -58,
  -66, 113, -25, -36, -81, 99, 42, 51, -28, -35, 30, 57, 121, 18, 70, -9,
  -12, 7, 69, 18, -170, -107, -29, 57, 27, -32, 0, 39, 3, 44, -17, 113, 55,
  -71, 78, 22, -46, -31, -36, 41, -80, -16, 0, 16, 16, 135, 63, -33, 39,
  -60, -6, -45, -153, -21, 115, 0, 95, -22, -109, 67, 50, -6, 27, -63, 79,
  110, 70, 104, 69, -161, -59, 19, 23, 193, 17, -71, -18, 57, 92, 66, 106,
  68, 6, 70, -106, -186, 28, -53, 116, 31, -41, 58, 93, 90, 41, 0, 53, 18,
  -62, -207, -11, -63, -1, -76, 90, 71, 47, 88, 149, 47, -114, -171, -73,
  -76, -69, -74, -15, -64, 84, 202, 29, 82, 37, -17, 99, 12, 82, -74, 120,
  37, 10, -27, -40, 44, 7, -5, 49, -96, 77, 127, 61, -73, -49, -4, -220, 70,
  -99, -186, 23, -32, 13, 106]

theorem fractionalNearFrameSubtreeG3R0038_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0038Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0038Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0038Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0038_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0038LowerBoundTable : List ℤ :=
  [-35, 56, 2, 184, 156, -121, 2, 101, 171, -205, -197, 252, 44, 226, 89,
  291, 91, 275, -85, 484, 239, 236, 325, -79, 357]

def fractionalNearFrameSubtreeG3R0038LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0038Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0038LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
