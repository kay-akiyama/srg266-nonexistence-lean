import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0225`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0225Mask : ℕ := 2488789283836516

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0225Witness : Array ℤ :=
  #[41, 135, 110, 97, 108, 2, -5, 13, -13, 28, 44, -101, -73, -124, -56,
  -62, 17, 57, 34, -9, -29, 3, -34, 14, -3, -7, 13, 4, 33, 75, -67, -89,
  -58, -10, -29, 83, 89, -54, -21, -42, -82, 47, 56, 51, 46, -42, 53, -2,
  -34, -38, -29, 25, -22, -51, -56, -42, -1, -20, -51, 2, -52, 38, -48, -17,
  27, 13, -54, 56, 22, 100, 37, 19, -62, -64, -33, 27, -77, 60, 93, 28, -10,
  -24, -46, 32, 65, 20, 61, 74, -37, -49, -27, 72, 67, 48, 23, 51, 13, -18,
  -23, -66, 50, -18, 14, 2, -17, 20, 0, 52, 17, 51, 9, 7, 54, -46, -27, -25,
  -75, -18, -46, 60, 23, 56, 8, -39, 0, -2, 16, 55, 6, 16, -7, -67, -25,
  -41, 75, 43, 6, 28, 35, 36, 31, -24, -17, 39, 46, 41, 23, 9, -92, -16, 0,
  26, 0, 2, 54, 1, -27, 1, -6, -49, -35, 31, -5, -4, 83, 55, 92, -55]

theorem fractionalNearFrameSubtreeG2R0225_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0225Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0225Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0225Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0225_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0225LowerBoundTable : List ℤ :=
  [-28, 47, 2, 39, 81, 1, 1, 12, 113, 9, 214, 189, 95, 41, -62, -12, 100,
  334, -62, 160, 178, 9, 364, 97, 10]

def fractionalNearFrameSubtreeG2R0225LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0225Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0225LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
