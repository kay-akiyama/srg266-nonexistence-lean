import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0148`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0148Mask : ℕ := 6848712124109602

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0148Witness : Array ℤ :=
  #[2, 65, -45, -95, 1, 10, 13, -10, -171, -118, -97, 285, 223, 219, 104,
  188, -97, 165, -27, -64, 150, 207, 134, 293, 26, 60, -70, -47, -228, -112,
  -40, 0, -16, 89, 66, 46, 84, -128, 81, 143, -49, -61, 14, -39, -43, 16,
  52, 62, 41, 156, -34, -75, -45, -72, 95, -18, -31, 19, -90, 131, 104, 53,
  51, 29, 17, 51, -40, 141, -25, -114, -1, -20, 61, -121, 54, 21, 22, -113,
  73, -86, 17, 134, 17, -40, 64, -11, 47, -203, 27, 43, 65, -71, 39, -72,
  60, -69, 18, 326, 19, -31, 59, 6, 30, -34, -4, 156, -49, 78, -79, 95, 74,
  94, -44, -194, -12, 42, -4, -172, 11, -116, -147, 264, 16, -103, 175,
  -101, -143, 65, 117, -29, -48, -141, 70, 64, 50, 150, 78, -103, 8, 125,
  -101, 91, 73, 61, 47, 55, -15, 138, 65, 54, 58, 114, -14, 10, -53, -72,
  18, -33, -60, -5, 68, -66, 21, 46, 0, 14, -59, 38]

theorem fractionalNearFrameSubtreeG3R0148_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0148Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0148Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0148Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0148_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0148LowerBoundTable : List ℤ :=
  [82, 76, 2, 27, 1, 333, 439, 209, 91, 520, -86, 558, -66, -74, 10, 96, 83,
  198, 70, 821, -141, 292, 708, 789, 617]

def fractionalNearFrameSubtreeG3R0148LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0148Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0148LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
