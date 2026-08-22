import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0126`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0126Mask : ℕ := 970134102917460

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0126Witness : Array ℤ :=
  #[51, 4, 92, -9, -84, 15, 10, 57, -12, 77, -57, -19, 0, -40, 41, 13, 44,
  47, 49, -99, -86, -93, -41, -66, 112, 35, 40, 39, 24, -29, -64, -165, 40,
  -29, -13, 34, 58, -58, 152, -49, -98, 0, -18, -41, -54, -14, 31, 16, -97,
  -8, 0, 209, -14, 32, 54, -59, 27, -28, 35, 19, -24, 3, -112, -31, -39,
  -70, 71, -20, 30, -103, 60, 69, -107, 120, 17, -65, -41, 86, 122, -53, -5,
  139, -27, -100, 39, 53, -63, 41, 57, 75, 7, 6, 97, 42, 24, 96, -10, 37,
  69, 69, 44, 26, 103, 141, -16, -18, 19, -43, 5, -19, -53, 113, 27, -1, 76,
  39, -24, -36, -25, -59, 69, 45, 49, 65, -108, -102, 0, 79, 104, -27, 55,
  45, 43, -1, 4, 30, -13, -61, 51, -6, -6, 21, 14, -55, -74, 38, 73, -45,
  -66, 67, -5, -5, -107, 74, 36, -93, -56, 55, -60, 67, 27, -67, -12, -4,
  80, -110, -33, 13]

theorem fractionalNearFrameSubtreeG1R0126_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0126Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0126Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0126Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0126_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0126LowerBoundTable : List ℤ :=
  [-36, -34, 29, 189, 146, 32, 65, 44, 2, 82, 79, 127, -176, 9, 198, -293,
  70, 504, 339, 316, 263, 163, 73, 11, 10]

def fractionalNearFrameSubtreeG1R0126LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0126Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0126LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
