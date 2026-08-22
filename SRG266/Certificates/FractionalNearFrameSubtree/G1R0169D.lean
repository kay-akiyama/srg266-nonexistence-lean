import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0169`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0169Mask : ℕ := 2447186080999969

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0169Witness : Array ℤ :=
  #[38, -30, -8, 32, -23, 0, 2, 50, 0, -35, 51, -44, 14, 0, 47, -22, -13,
  -12, 64, -91, -40, -87, 16, 52, -114, -91, -59, -33, 46, 99, 76, 131, 27,
  -18, 19, -7, 12, -29, 1, -23, 15, -45, -34, -5, 10, 15, 16, 17, 35, 3, -4,
  -30, 22, 11, -4, -35, -22, -43, -26, 14, 36, 43, 23, 13, -1, 28, 23, 16,
  48, 34, 11, 27, 13, 4, -9, 21, 16, -2, 10, 19, 23, 2, 10, 10, -37, -31,
  -15, -29, 27, 1, 44, -10, 2, -10, -13, -11, -1, 33, 15, 8, 0, 20, -3, -2,
  -1, -28, 23, 2, 15, 10, 51, -27, -40, -12, -46, -36, -5, 11, -45, -2, -26,
  -19, 22, 2, 37, -1, -5, -52, -22, -10, 16, -6, -33, -3, 14, -10, -7, 30,
  21, 26, 22, -18, 16, 12, -16, -10, 6, -24, -48, -24, -2, 26, 9, 8, 1, 21,
  15, 33, -27, 31, 44, 13, 4, 8, 27, 27, 34, -5]

theorem fractionalNearFrameSubtreeG1R0169_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0169Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0169Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0169Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0169_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0169LowerBoundTable : List ℤ :=
  [-8, 17, 6, 1, 2, 36, 41, 135, 34, 11, -44, -21, 11, 15, -1, 37, 11, 115,
  -147, 130, 117, 60, 18, -76, 220]

def fractionalNearFrameSubtreeG1R0169LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0169Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0169LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
