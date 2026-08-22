import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0408`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0408Mask : ℕ := 5742490069543344

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0408Witness : Array ℤ :=
  #[11, 17, -133, 3, 10, -104, 57, -95, -15, -52, 71, 59, 78, 54, 11, 23,
  -8, -25, -11, -15, -9, -6, -25, -61, 123, 18, 19, 4, -62, -32, -66, 28, 5,
  35, 14, -14, -50, 38, 3, 26, 63, 14, 0, 95, 66, 36, -48, -54, -20, -10,
  -18, -36, -54, -46, 50, -8, 28, 43, 0, -92, 0, -55, 26, -42, 50, 109, 11,
  -7, 79, -19, 22, 6, -86, 23, 14, -41, -3, 19, 94, 5, -44, 23, 23, 18, -26,
  8, -11, -26, -2, -41, 54, -1, -18, -11, 37, -48, -30, 29, -28, -20, -28,
  52, 56, -19, 62, -1, 63, 60, 45, -47, 4, -46, 3, 50, 28, 4, 21, 41, 77,
  -35, 35, -80, 6, -73, -16, 19, -60, -20, -32, -4, -6, -13, -21, 51, -18,
  10, -7, -20, -9, -21, 57, -4, -4, -15, 85, 24, 8, -39, -22, -23, 39, 57,
  -8, 22, -16, -24, 32, 42, 9, -28, -24, -24, -11, -43, 11, -21, -11, -6]

theorem fractionalNearFrameSubtreeG2R0408_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0408Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0408Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0408Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0408_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0408LowerBoundTable : List ℤ :=
  [-46, -20, 8, 8, -7, 71, -78, 41, -22, 8, 121, -185, 82, -36, 95, 59,
  -122, -19, 151, 100, -139, 210, 216, 96, 310]

def fractionalNearFrameSubtreeG2R0408LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0408Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0408LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
