import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0148`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0148Mask : ℕ := 1039742346504872

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0148Witness : Array ℤ :=
  #[-72, 36, 110, 79, -78, 60, -3, -1, -93, -110, 109, 52, 59, 95, -41, 58,
  49, 76, -64, 52, 32, -76, -48, -57, 48, 68, 41, 27, -60, -108, 2, -13,
  -23, 59, 88, 66, -26, -25, 4, 54, 61, 51, 55, 24, -27, 12, 33, -38, -3,
  13, -7, 35, -24, -104, 11, 55, -36, -62, 59, -25, -3, -81, -80, -21, 60,
  6, -22, -7, 74, 16, -16, 8, -93, -31, -5, 20, 91, 82, -22, 75, 63, -122,
  55, -53, 37, 50, 6, 58, 79, 60, 53, -30, -74, 87, 76, 8, 40, 62, 63, -47,
  54, -112, 96, 44, -106, 12, -101, -38, -42, 22, 121, 51, -107, -62, 17, 6,
  1, -3, -6, -6, -64, 35, -17, -8, 31, 0, -50, -11, 5, -7, -35, 28, 53, -19,
  5, -18, 29, 45, 48, -63, -58, -34, 48, -1, 25, 41, -29, 101, 50, 60, -16,
  -12, -29, -74, -50, -45, -34, -15, 33, 47, -25, 28, 35, 17, 63, 2, -88,
  105]

theorem fractionalNearFrameSubtreeG1R0148_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0148Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0148Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0148Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0148_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0148LowerBoundTable : List ℤ :=
  [0, 28, 2, 123, 1, 123, 92, 11, 65, 72, -99, 59, -71, -5, 238, -17, -6,
  407, 130, 273, 240, 245, 50, 94, 286]

def fractionalNearFrameSubtreeG1R0148LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0148Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0148LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
