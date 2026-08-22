import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0627`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0627Mask : ℕ := 11297991701287953

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0627Witness : Array ℤ :=
  #[59, 148, 86, 127, 165, 92, 15, 54, 102, 113, 103, 159, -168, -234, -200,
  -218, -165, -120, 21, -158, -40, -138, -11, 0, -224, -140, -40, -10, 177,
  189, 252, 300, 41, 62, 57, 49, -25, -43, 53, -6, -30, 13, 19, -49, 37, 18,
  16, 35, 40, -5, -1, -24, 48, -20, 58, -22, 6, -20, 4, 0, 40, 4, 18, -53,
  -15, -14, -8, 60, -5, -1, -9, 29, 34, -23, 18, 9, 32, -21, 14, 11, 13, -6,
  -1, -5, -24, -7, 52, -1, 9, 9, -15, -11, -48, -23, -11, -11, 7, -22, 32,
  60, 29, 59, 16, 53, -19, -30, 25, 45, 37, 50, 4, -29, 23, 17, -83, 36,
  -45, -40, -4, 34, -25, -13, 17, 45, 10, -22, 32, -2, 31, -20, -7, -7, -25,
  -5, -7, -39, 39, 9, 1, -2, 13, -35, -21, -17, 61, 26, 54, 62, -27, 7, -28,
  8, 43, -35, -20, 85, -59, -16, 22, 50, -18, 4, -37, 61, 8, -41, 42, 0]

theorem fractionalNearFrameSubtreeG2R0627_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0627Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0627Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0627Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0627_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0627LowerBoundTable : List ℤ :=
  [61, 2, 79, 24, 236, 151, 92, 108, 3, -7, -74, 57, 73, 233, -31, 68, 112,
  -69, 149, 117, 91, 234, 11, 211, 93]

def fractionalNearFrameSubtreeG2R0627LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0627Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0627LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
