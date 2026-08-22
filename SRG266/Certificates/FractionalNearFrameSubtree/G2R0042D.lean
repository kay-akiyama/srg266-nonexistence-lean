import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0042`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0042Mask : ℕ := 901139857379425

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0042Witness : Array ℤ :=
  #[-53, -65, -117, -43, -165, -216, 149, 148, 102, 105, 86, 0, 65, 68, -10,
  18, 56, -4, 2, 48, 8, -60, -45, -74, 101, 46, 15, 1, 31, -46, -36, 14, 27,
  31, 27, -34, 6, 74, -78, -83, 34, 6, 37, 70, 64, -56, -19, -9, 27, -10,
  53, 75, -39, 62, -63, -18, -101, -37, -1, -32, 20, 0, 52, -70, 0, 38, -49,
  -2, 51, 6, -8, -5, 66, 11, 24, 16, 23, -130, -15, -10, -35, 66, 24, 114,
  91, -36, -10, 24, 65, 75, 3, 18, 8, -41, -24, -17, -21, -14, 9, 59, -17,
  104, 36, -34, -33, 67, 40, -16, -34, -10, -136, 67, 46, 0, 19, 62, 22,
  -92, -71, -64, -1, -49, 19, -51, -40, -69, -46, -27, -21, -13, -24, 40,
  -91, -59, 169, -14, 6, 7, -11, -19, -108, 12, 63, -13, 5, -9, 51, 38, -23,
  41, 62, 79, 92, 9, -8, 38, 13, 56, 46, -102, 62, 78, -75, -40, -60, 25,
  -51, 0]

theorem fractionalNearFrameSubtreeG2R0042_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0042Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0042Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0042Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0042_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0042LowerBoundTable : List ℤ :=
  [-38, 2, 25, 84, -89, 33, 87, 84, 38, -63, 109, 94, -82, 105, 227, 10,
  -151, -29, 363, 47, 92, 80, -108, 10, 218]

def fractionalNearFrameSubtreeG2R0042LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0042Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0042LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
