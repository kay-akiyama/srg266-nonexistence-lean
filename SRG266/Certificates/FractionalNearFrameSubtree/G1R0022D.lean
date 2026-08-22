import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0022Mask : ℕ := 450642365239813

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0022Witness : Array ℤ :=
  #[16, 6, -52, -28, -46, 9, -15, -13, -46, -34, -33, -1, -8, 44, 31, 9, 25,
  45, -37, 46, -20, -56, 6, -36, 9, -19, -29, -7, 12, 5, 25, 31, -4, -31,
  -29, -80, 43, -5, 12, 29, 18, 22, 15, 44, -27, 0, 44, 23, 60, 64, -79,
  -65, -41, -34, -20, -18, -7, -2, -12, -57, -16, 45, 19, 2, -18, -13, 6,
  -1, 42, -31, 85, 10, 23, 16, 25, -28, 33, 15, -95, -7, 27, 15, 46, 25, 19,
  -18, 28, 22, 9, 7, 88, 6, 48, 17, 9, 32, -1, 32, 32, 2, -36, 17, -6, -53,
  32, -20, 29, -68, 27, -37, -18, -4, -56, 34, 59, 33, 11, -24, -34, 10,
  -52, -21, -43, -21, 2, -33, 21, -28, 39, -36, 9, 17, -29, 28, -38, 9, -21,
  -13, 7, 27, -50, 28, 4, 17, -3, -8, -5, 5, -23, 19, 34, -24, 29, -30, 17,
  -52, 3, 29, 20, 38, -20, -11, -2, -4, 0, -8, -25, -28]

theorem fractionalNearFrameSubtreeG1R0022_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0022Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0022Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0022Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0022_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0022LowerBoundTable : List ℤ :=
  [-51, -74, -51, 88, 2, 31, 1, -21, 0, -103, 164, -120, 77, -61, 127, 11,
  -98, 25, -76, 134, 178, -58, -16, 35, 9]

def fractionalNearFrameSubtreeG1R0022LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0022Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0022LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
