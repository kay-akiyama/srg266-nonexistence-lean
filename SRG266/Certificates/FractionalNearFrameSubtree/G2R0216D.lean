import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0216`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0216Mask : ℕ := 2370098919355409

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0216Witness : Array ℤ :=
  #[-8, 0, -24, 33, -55, -26, 1, -18, -31, 8, 67, -22, 29, 7, 0, -13, -90,
  9, 39, 28, -11, -73, -6, 15, 65, 29, 3, -4, -17, 86, -44, 69, 18, 7, 22,
  53, -46, 0, -101, -10, 30, 21, -26, -97, 26, 21, 21, 21, 43, -44, -46, 19,
  27, 57, -41, -13, -46, -29, -6, 47, 21, 40, 36, -14, -33, 15, 4, 72, 38,
  -26, -6, -5, 19, -82, -36, 67, 53, 22, 44, -21, -62, -21, -70, 111, -13,
  -63, 3, 97, -69, -33, 38, 60, -15, 62, 46, -12, 21, -35, 6, -95, -24, 16,
  57, 42, 16, 19, 30, -22, 64, 84, 5, -57, -56, -137, -14, 40, -32, 37, 95,
  1, -10, 17, -39, 9, -43, 135, -67, 61, -6, 29, -12, -97, 183, 25, -13, 96,
  118, 58, -30, -32, 38, -49, 48, -34, 54, 1, 18, -9, 10, 53, 18, 25, 29,
  65, 84, -107, -51, -76, -18, -59, -130, 2, 28, 13, -22, 17, 104, -47]

theorem fractionalNearFrameSubtreeG2R0216_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0216Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0216Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0216Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0216_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0216LowerBoundTable : List ℤ :=
  [15, 135, 21, 82, 1, 91, 2, 29, 21, 34, -57, 152, 23, 241, 2, 156, 8,
  -115, 227, 269, 52, -87, 28, 137, 10]

def fractionalNearFrameSubtreeG2R0216LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0216Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0216LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
