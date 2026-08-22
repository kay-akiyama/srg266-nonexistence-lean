import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0003Mask : ℕ := 523834918551683

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0003Witness : Array ℤ :=
  #[25, 26, 26, 19, -25, -29, -17, 24, 0, -25, -47, -66, -13, 85, -68, -25,
  34, 13, 22, 68, -118, -73, 48, 91, 80, 0, 6, -6, -81, -74, -32, 47, 10,
  35, -10, -15, 46, 5, 47, 18, -105, -49, -97, -62, 60, 11, -10, 12, 33, 73,
  17, -4, -2, -60, -16, -9, -74, 0, 3, -93, -49, 1, 7, -4, 35, -25, 94, -33,
  -23, -104, -8, -36, 27, -12, 18, -21, 11, 44, -80, -69, 1, 36, -47, -48,
  72, 99, 17, -35, -17, 11, -6, -13, 38, -1, 169, 20, -125, 2, -4, -1, -43,
  53, -23, 118, 29, 52, -106, -101, -90, -58, -74, 52, -75, -25, -4, 5, 86,
  -8, -43, -44, -107, -40, -90, 52, 8, 24, 45, -41, -26, 29, -7, 30, -37,
  -15, -30, -16, 0, 19, 67, -47, -72, 34, -7, 45, -44, 87, 10, -29, 51, -34,
  7, 46, 42, 2, -62, 0, 65, 5, 52, -82, 3, -79, 23, -36, 74, 18, -57, 70]

theorem fractionalNearFrameSubtreeG5R0003_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0003Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0003Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0003Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0003_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0003LowerBoundTable : List ℤ :=
  [-119, -89, 2, -128, -24, -21, -40, -66, 0, 263, 10, -53, -316, -211, 72,
  -129, 57, -38, 75, 21, -85, 8, -111, -118, 35]

def fractionalNearFrameSubtreeG5R0003LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0003Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0003LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
