import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0019Mask : ℕ := 885643347332099

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0019Witness : Array ℤ :=
  #[8, -32, 0, 0, 16, -36, -117, -29, -149, 0, -208, -18, 65, 3, 136, 106,
  143, 177, 26, 136, 23, -19, 128, 18, -51, 71, 59, -81, -24, 44, -79, -90,
  -28, -10, 7, -17, 19, -68, 58, 4, 0, 75, -56, -106, 92, -70, 257, -57, 91,
  -54, -102, -70, 34, 100, -75, -89, 169, 65, 28, 0, -54, -10, -2, -8, 70,
  -34, 42, 11, 28, -108, -65, 19, -36, 16, 70, -19, 35, 79, 56, -105, 20,
  114, -84, 25, -53, 102, 13, 33, -9, -165, -65, 16, -28, -8, -91, 20, 26,
  80, -95, -23, -48, -21, 39, -23, -1, 48, 55, 84, 102, 52, 33, 52, 42, 48,
  118, 35, 128, 107, 123, 88, -42, 21, 5, 106, 77, -60, -56, 80, -33, 112,
  -5, -72, 172, -116, 0, 101, 11, 72, -93, 54, 13, -108, 27, -45, 144, -34,
  80, 55, 74, -18, 48, -1, 101, 41, -52, 65, -65, 32, -143, 14, 10, -19, 27,
  -52, -101, -20, -33, -111]

theorem fractionalNearFrameSubtreeG3R0019_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0019Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0019Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0019Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0019_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0019LowerBoundTable : List ℤ :=
  [3, 131, -2, 174, 17, 1, 141, 16, 134, 411, 223, 245, 473, 16, 377, 59,
  157, -48, -13, 385, 292, 10, 231, 9, 221]

def fractionalNearFrameSubtreeG3R0019LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0019Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0019LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
