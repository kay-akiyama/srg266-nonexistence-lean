import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0529`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0529Mask : ℕ := 6780365969988129

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0529Witness : Array ℤ :=
  #[-31, 71, -13, 59, -25, -83, 144, -7, 99, 92, -6, 117, 0, 37, 33, -52,
  -50, 0, 35, -62, 4, -77, 25, 15, -6, 53, -55, 6, 49, 7, 0, 112, -10, 45,
  27, 70, -54, -80, 64, 70, 43, 16, 64, -79, -31, -52, -58, 30, 18, 94, -7,
  15, 7, 44, 4, 18, 46, 11, 46, -22, 21, 74, 12, 18, -53, 9, 6, 7, -44, -66,
  -18, 42, -34, 35, -8, 40, 16, -28, 20, 15, -101, -47, -24, -30, 43, -42,
  14, 61, -75, 35, -6, 42, 38, 8, 5, 12, 10, 16, -63, 72, 94, -6, 29, -24,
  29, 64, 53, 10, 42, 13, -31, 36, 47, 15, 21, -21, -55, 0, -27, 70, 21, 5,
  17, -8, 21, -2, 12, 9, 2, -3, 0, -6, 19, -16, -28, -2, 29, 25, 39, -33,
  21, 6, -52, -16, 5, 13, 9, -24, 31, 31, -14, 17, -39, 14, 21, 14, 13, -34,
  3, 9, 10, 20, -37, 94, 37, 52, -6, -70]

theorem fractionalNearFrameSubtreeG2R0529_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0529Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0529Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0529Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0529_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0529LowerBoundTable : List ℤ :=
  [83, 60, 62, 1, 19, 253, 105, 289, 128, 150, 10, -46, 179, 125, 153, 56,
  74, -116, 211, 63, 100, -24, 167, 148, 319]

def fractionalNearFrameSubtreeG2R0529LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0529Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0529LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
