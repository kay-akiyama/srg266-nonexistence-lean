import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0080`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0080Mask : ℕ := 2370123347205137

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0080Witness : Array ℤ :=
  #[-55, -59, -40, -80, -24, -62, 20, 90, -133, 0, 23, -24, 13, 124, 19, 0,
  -39, 40, 90, 9, -14, 54, -10, -19, -3, -52, 50, 12, -39, -67, -74, 52, -8,
  -13, -6, 107, -40, -120, -50, 29, -27, -62, -28, 3, 18, 78, -55, -23, 7,
  -24, 23, 166, -30, 73, 72, 6, -42, 1, -7, -53, 111, 59, -28, -5, 65, 135,
  -18, 25, -17, 3, 93, 41, -25, 16, -20, 114, 37, 113, 124, -110, 29, 156,
  -25, 5, -75, 19, 86, -86, 55, -42, -79, 27, -58, -1, -60, 17, 100, -51,
  79, -31, 19, -107, 103, 59, -50, 42, 75, -21, 59, -21, 16, 49, -34, 17,
  -33, -55, -2, 81, -86, 1, -94, 103, 35, 46, 29, -34, 83, 76, 54, 35, 0,
  -57, -93, -85, 45, -27, 23, 22, 116, 94, -159, 60, 131, -56, 27, -139,
  -57, 0, 51, 20, -30, -112, -68, 56, -6, -51, -43, 21, 87, -28, -50, 117,
  39, 23, 56, 31, 56, 69]

theorem fractionalNearFrameSubtreeG3R0080_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0080Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0080Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0080Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0080_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0080LowerBoundTable : List ℤ :=
  [-26, 34, 321, 155, 49, 1, 83, -111, -13, -96, 80, 208, 142, 252, 163, 34,
  223, 176, 10, 263, 59, 11, 131, 374, 10]

def fractionalNearFrameSubtreeG3R0080LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0080Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0080LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
