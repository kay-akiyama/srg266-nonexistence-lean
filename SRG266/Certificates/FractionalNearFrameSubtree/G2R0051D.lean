import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0051`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0051Mask : ℕ := 936554836755018

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0051Witness : Array ℤ :=
  #[10, -75, 22, -10, 25, 53, 3, 86, 9, 69, 40, 0, -23, -68, -104, -65, -30,
  -1, 23, 71, -55, 67, 51, 15, 81, -12, 36, -81, -27, 63, -37, 68, 59, 50,
  100, -88, -40, -2, 67, -106, -61, -155, 14, 6, 83, -5, 55, -15, 16, -16,
  37, -46, -36, 44, -9, -119, 61, -69, 99, 21, 110, 63, -9, -51, 16, 107, 4,
  77, -63, -71, -15, -20, 40, 2, -83, 67, -8, 25, 43, 35, 65, -128, -70,
  -16, -77, -83, 26, -34, 18, -21, -15, 44, 32, -49, 77, -42, 3, -64, -53,
  41, 5, 37, 76, -9, -91, -11, -27, 31, -33, -83, 1, -28, 35, 71, 28, -2,
  26, -16, 64, 62, -8, -29, -8, 23, -27, 61, 24, 3, -63, 19, 50, 56, 17,
  -23, -26, -2, 23, 29, -8, -32, 88, -15, 32, 22, 0, 45, 2, 111, 48, -37,
  -19, -29, 4, 2, 5, -43, -15, -15, -20, 105, 52, 35, 26, -65, 40, 107, 42,
  -101]

theorem fractionalNearFrameSubtreeG2R0051_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0051Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0051Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0051Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0051_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0051LowerBoundTable : List ℤ :=
  [-4, 158, 2, -67, 64, 2, 78, 1, 40, 125, 54, 236, 9, 193, 131, -173, 83,
  248, -2, 151, 9, 86, 199, 169, -42]

def fractionalNearFrameSubtreeG2R0051LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0051Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0051LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
