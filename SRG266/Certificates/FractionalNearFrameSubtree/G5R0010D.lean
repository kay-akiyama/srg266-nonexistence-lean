import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0010Mask : ℕ := 828575185862723

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0010Witness : Array ℤ :=
  #[-84, -57, -107, 9, -73, 0, 25, -51, 37, -11, 40, 44, 76, 0, 88, 1, -56,
  -71, -71, -5, -64, 12, 47, -41, 82, 20, 60, 25, 24, 10, -2, 32, 58, 42,
  169, -96, 77, 106, -147, -96, -121, 0, -72, -4, -110, 38, -25, -67, 22,
  101, 47, 28, -70, 45, 26, -7, -11, -30, 71, 6, 38, 73, -3, -22, -58, 28,
  -119, 172, -65, -43, 78, 43, 55, 6, 7, 76, 59, 49, 63, 72, 97, 45, 19, 11,
  19, -43, -21, 57, 94, -85, 88, 48, 54, 33, 29, 6, -31, 141, -97, -68, 98,
  71, -6, -21, -20, 19, -4, 53, 115, -139, -148, -118, 86, -1, -65, -26,
  -14, -45, -82, 16, 48, 68, 34, 45, 28, -88, -57, 20, 5, -155, -154, 74,
  191, -47, -45, -88, 17, 106, 68, 5, -34, 82, 107, 4, 57, -64, 23, 57, 67,
  169, -45, 228, -117, -45, -67, -104, 44, -98, -6, -49, 22, -128, 11, 43,
  46, -35, -7, -21]

theorem fractionalNearFrameSubtreeG5R0010_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0010Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0010Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0010Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0010_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0010LowerBoundTable : List ℤ :=
  [-15, 44, 3, -24, 139, 54, 33, 65, 2, 37, 10, 10, 186, 156, -155, 451, 11,
  82, 10, 175, 371, 56, 141, 130, 65]

def fractionalNearFrameSubtreeG5R0010LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0010Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0010LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
