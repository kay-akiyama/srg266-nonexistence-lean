import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0005`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0005Mask : ℕ := 266886736420995

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0005Witness : Array ℤ :=
  #[66, -25, -37, -5, 0, -26, 11, 0, 15, -74, -29, -27, 74, 41, -22, 9, -66,
  -13, 4, -57, -34, -109, 42, -106, 22, 69, 20, -39, -4, 70, -20, 40, -9,
  94, 65, -3, 17, -66, 38, 25, 0, -4, -66, -111, -49, 82, -56, 42, 64, 119,
  0, -42, -43, -41, -40, -10, -99, 15, 25, 0, -21, -11, -13, -8, 14, -3, 42,
  39, 19, -78, 42, -51, -3, -21, -33, -17, 40, 75, -13, 6, -76, 31, -17,
  -50, 19, 18, 71, 54, 32, -20, -60, -68, -67, -62, 4, -29, -28, 46, -2, 57,
  -25, 29, 9, 31, -6, 28, 23, 160, -47, -26, -5, 0, -52, -3, 3, -44, -97,
  44, -15, 7, 69, 45, -2, 75, 39, 5, 41, -49, 64, -36, 1, 84, 5, -2, 35, 3,
  -58, -18, -25, -31, 40, -16, 72, 32, -3, -10, 40, 40, 17, 27, 12, 22, -8,
  31, 70, 16, -102, -29, -29, 39, 11, -88, 44, 106, -135, 11, -4, 36]

theorem fractionalNearFrameSubtreeG3R0005_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0005Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0005Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0005Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0005_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0005LowerBoundTable : List ℤ :=
  [-50, 48, 40, -74, 3, 2, 2, -33, 73, 150, 58, 9, 98, 224, 9, 33, 96, -22,
  -163, -102, 8, -49, -115, 7, 238]

def fractionalNearFrameSubtreeG3R0005LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0005Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0005LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
