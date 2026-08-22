import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0102`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0102Mask : ℕ := 954131658948948

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0102Witness : Array ℤ :=
  #[-24, 90, 48, 108, 23, -38, 28, -23, -19, 1, -44, -18, 30, -39, 6, 51,
  15, -33, 6, -21, 19, -45, -77, -45, 78, 23, 65, 10, 16, 12, -56, -4, 27,
  -20, -41, 100, -29, 42, -27, -69, 70, 14, 60, 15, -13, 20, -56, -46, -35,
  -30, 32, 11, -34, -62, 66, 58, -39, -43, 16, 32, -53, 36, 2, 18, 32, 53,
  -64, 24, 68, -28, -12, -52, 86, -55, -32, 30, -38, 78, -26, 4, -63, 54,
  -10, 92, -14, -57, 7, 85, -41, 27, 32, 2, 88, 37, 3, 0, -34, 81, -7, 70,
  61, 51, -21, 13, -25, 41, 49, -56, -32, -23, 64, 41, -25, 13, -27, 33, 58,
  2, 58, 64, -67, 32, 23, -53, -17, 20, 40, -18, -52, -8, 36, -72, -32, 3,
  1, -47, 10, 19, 22, 84, 22, 59, -15, -33, 25, 45, 14, 32, 56, 38, -2, 25,
  -52, 7, -17, 44, 30, -26, 37, -30, 27, 0, -54, 49, -40, -19, -19, 62]

theorem fractionalNearFrameSubtreeG1R0102_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0102Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0102Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0102Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0102_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0102LowerBoundTable : List ℤ :=
  [1, 86, 112, 128, 100, 47, 98, -26, -61, 189, -37, 159, 91, 14, 333, 253,
  -168, 230, 125, 258, -68, 167, 403, 11, 138]

def fractionalNearFrameSubtreeG1R0102LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0102Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0102LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
