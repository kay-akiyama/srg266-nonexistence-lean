import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0017`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0017Mask : ℕ := 677057171933457

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0017Witness : Array ℤ :=
  #[-64, -54, 0, -86, 29, -82, -3, 112, -12, -53, 0, 28, 24, 84, 180, -65,
  12, 8, -80, 50, 41, -46, -83, 38, 42, 86, 50, 86, -57, -13, -47, -99, -31,
  -51, -72, -105, 15, 80, 28, 108, -118, -5, -73, 88, -50, 72, 5, -101, -36,
  91, 128, 23, -29, -8, 94, 81, -32, -70, -53, 34, 15, -17, 10, 49, 47, 115,
  -43, 58, 44, -75, -70, -51, 81, 49, 79, 19, -114, 33, 2, 56, -70, 91, 32,
  0, 50, -10, -45, 61, -14, -13, 114, 59, 16, 47, -17, 36, 24, -29, 63, 10,
  -12, 49, 76, 95, -32, -15, 23, 5, -5, -11, -131, -56, 58, 61, -56, -7,
  -43, 58, 25, 5, -55, -22, -14, -137, 106, -3, 119, -90, 8, -146, 24, -52,
  59, 92, -99, 5, 30, 64, -37, -36, 55, 12, -14, 40, -62, -129, 31, 6, 21,
  40, -208, 80, 68, -93, -124, 76, -51, 38, -29, -26, -47, -35, 6, 18, 38,
  80, 55, 0]

theorem fractionalNearFrameSubtreeG2R0017_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0017Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0017Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0017Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0017_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0017LowerBoundTable : List ℤ :=
  [-66, -83, -22, 38, -2, 0, 1, 98, 47, -61, 234, -232, 141, 18, -105, 112,
  10, 239, 89, 307, 334, -94, 10, 241, 377]

def fractionalNearFrameSubtreeG2R0017LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0017Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0017LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
