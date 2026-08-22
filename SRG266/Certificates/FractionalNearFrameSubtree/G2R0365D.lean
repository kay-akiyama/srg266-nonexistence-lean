import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0365`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0365Mask : ℕ := 5715916341584204

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0365Witness : Array ℤ :=
  #[27, 46, 114, 28, 50, 64, 33, 31, 69, 71, 6, 9, -4, -56, -101, -133, -68,
  23, -70, -59, -44, 33, -3, 83, 32, 1, 39, 3, -8, -4, 15, -46, -62, 15,
  126, 50, 101, 60, -6, 47, -37, 26, 0, 0, 71, 16, 43, 98, 83, 63, -150,
  -79, -58, -33, 75, 20, -72, -138, -8, 1, 13, 131, -7, -59, -39, 69, 3, 45,
  -22, 27, -106, 45, -26, 92, 112, 48, -13, 132, 20, -35, 24, 30, 19, 61,
  -78, 74, -58, 44, 26, 51, 28, 73, -111, 39, -55, 6, -25, 55, -55, 28, -52,
  159, 137, -96, -96, 4, 16, 11, -11, 1, 81, 42, -124, -15, -81, -29, -96,
  61, 22, -144, 11, -110, -92, -18, 110, 34, -9, 52, -25, -12, -24, 82, 8,
  61, 43, 60, -118, 64, -1, 41, 20, 49, 35, -10, -8, 27, -45, 27, -35, 9,
  13, 18, 47, 45, 12, -75, -34, 41, 4, 39, -69, 0, -46, 69, -24, -1, -48,
  67]

theorem fractionalNearFrameSubtreeG2R0365_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0365Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0365Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0365Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0365_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0365LowerBoundTable : List ℤ :=
  [-17, 2, 2, 60, 56, 2, 150, -29, 274, 60, 226, 62, 21, 238, 239, -130,
  161, 11, -98, 79, 250, 414, 175, 333, 19]

def fractionalNearFrameSubtreeG2R0365LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0365Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0365LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
