import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0189`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0189Mask : ℕ := 6866848082435604

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0189Witness : Array ℤ :=
  #[-21, -21, -35, -46, -44, -59, -240, -107, 94, -46, 22, 42, 77, 50, 52,
  58, -18, 58, 39, 86, 33, -76, -109, -65, 6, 5, -18, 10, -31, -21, -59, 27,
  -42, -12, 38, 23, 58, 71, -20, -64, -48, -7, -5, -89, 4, -32, 47, 39, 14,
  25, -56, -34, -10, -45, -25, -47, -91, 1, 2, -3, 105, 63, 116, -38, 90,
  -14, -60, -26, 12, 51, -33, 34, 32, -125, 41, -10, -33, -10, 74, 29, 17,
  -78, 49, 62, -69, 86, -40, 70, 25, 12, 19, 101, 12, -87, 20, -1, -3, 57,
  38, -4, -27, -96, 9, 22, 17, -19, 31, -118, 15, -44, 51, 13, -6, -37, -20,
  -119, -175, -104, 18, 99, 6, 76, 48, 96, -175, -30, 39, 17, -3, 31, 33,
  -82, 23, -65, -3, -118, 43, -107, 67, 42, 173, 93, 94, 38, 0, -67, 32, 15,
  -7, -47, 27, -37, 10, 109, -35, 44, -33, 59, -38, 16, -1, 19, -7, 4, -36,
  10, 17, -20]

theorem fractionalNearFrameSubtreeG3R0189_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0189Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0189Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0189Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0189_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0189LowerBoundTable : List ℤ :=
  [-111, 13, -67, 61, 1, 2, -6, -50, -57, 191, 10, 21, 8, -77, 11, 23, 8,
  117, 10, 9, -48, 120, 158, -72, -228]

def fractionalNearFrameSubtreeG3R0189LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0189Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0189LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
