import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0171`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0171Mask : ℕ := 1380481563042148

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0171Witness : Array ℤ :=
  #[-24, -6, 175, -30, -47, 5, 20, -20, 68, -25, 28, -104, 68, 21, 32, 0,
  -101, 20, 134, 18, -27, 33, 15, -8, 26, 19, -12, -2, 28, 34, -38, -51, 36,
  -91, 103, -78, -82, 146, 109, 91, 77, -28, 42, -115, 196, -18, 0, -25, 7,
  -6, -59, 34, 45, -36, -5, 32, 0, 35, 155, 166, 29, -208, 27, -48, -193,
  -203, -19, -153, -197, 22, -30, 76, -3, 111, 10, 4, -117, 66, 21, -26, 4,
  71, 13, 64, -22, -95, 21, 38, 30, -12, 13, 2, -50, -96, 28, 33, 73, 53,
  38, 6, 23, -1, -2, -32, 35, 49, 30, 38, 9, 97, -39, 60, -45, 15, 31, -30,
  16, -86, -16, 99, -26, -23, -32, 47, 5, 88, 17, -16, 0, 48, 62, 78, 25,
  -1, 44, -7, -18, 39, 60, 20, 127, -32, -3, 124, 3, 19, 57, -22, 22, -54,
  24, 25, -7, -1, 104, 4, -25, 31, 69, -155, 89, 88, -6, -55, 40, -30, 60,
  21]

theorem fractionalNearFrameSubtreeG2R0171_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0171Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0171Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0171Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0171_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0171LowerBoundTable : List ℤ :=
  [25, 163, 188, 144, 177, 1, 105, 29, 115, 131, 170, 403, 145, 331, 56, -3,
  328, 390, -73, 74, 58, 190, 10, -340, 124]

def fractionalNearFrameSubtreeG2R0171LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0171Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0171LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
