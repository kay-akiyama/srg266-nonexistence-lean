import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0062`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0062Mask : ℕ := 798019439643404

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0062Witness : Array ℤ :=
  #[128, -30, -52, 53, -56, -105, 15, 3, 86, 107, -3, 43, -59, 7, 19, 96,
  -62, 41, -102, -1, 77, 3, 24, 59, -53, 9, -29, -2, 121, 10, 50, -46, 9,
  -1, -74, -77, 41, 1, 74, -51, 31, 38, 99, 73, 70, -23, 9, -14, 31, 1, -95,
  30, -18, 131, -24, -2, -69, -23, -26, -75, -36, 27, 0, -46, -1, 133, -47,
  -48, 20, -39, 14, 41, 60, -13, 92, 8, 30, 28, 28, 3, 15, 14, -15, -56, 30,
  -25, 47, -43, -78, -123, -6, -22, -65, 60, 5, 11, 56, 81, 17, 51, 44, 57,
  21, 56, -18, -40, -91, 14, 15, 31, -24, -62, 80, 41, 21, 57, 24, -8, -11,
  30, -28, -90, -1, -20, 24, 27, -35, -24, 59, 1, -29, -76, 26, -45, 46, 0,
  10, 39, 37, -24, 34, -30, -38, 64, -56, -19, -38, -2, 22, -28, 1, -54,
  -40, 13, 47, 37, -77, -48, -33, 51, -30, 7, 13, 44, 6, -24, 109, 118]

theorem fractionalNearFrameSubtreeG1R0062_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0062Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0062Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0062Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0062_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0062LowerBoundTable : List ℤ :=
  [-32, 1, 148, -51, 2, 2, 2, 0, 79, 25, -101, 107, 112, 110, 54, 285, 271,
  241, 10, 93, 139, -116, 312, 221, 426]

def fractionalNearFrameSubtreeG1R0062LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0062Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0062LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
