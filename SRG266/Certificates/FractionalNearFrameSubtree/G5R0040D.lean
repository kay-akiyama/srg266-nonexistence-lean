import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0040`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0040Mask : ℕ := 2165027838067042

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0040Witness : Array ℤ :=
  #[83, 32, -2, -27, -52, -19, 0, -23, -11, 39, 27, 68, -47, 0, -27, -47,
  -8, -15, 49, -5, -28, -31, -30, 10, -51, -12, 2, -25, 9, 49, 122, 0, -55,
  -15, -133, -6, -17, -21, 127, -10, -36, -22, -7, 33, -20, -50, -92, -6,
  72, -71, -47, 58, 52, 8, 31, 65, 42, -9, -94, -77, 7, 27, -6, -7, -7, -16,
  27, -41, -25, 29, 17, 27, 1, -20, -63, 17, 16, 78, 5, 29, 26, -18, -9, 22,
  38, 30, -38, 7, -1, -1, -18, 68, 83, 19, 1, -11, 38, -112, 38, 110, 52,
  10, -1, -28, 49, -3, 28, 38, 70, -9, 45, -38, -21, -11, -58, -22, 19, -27,
  78, 5, 16, -14, 13, -21, 1, -51, 72, -18, 27, 37, 75, 19, -104, 70, 37,
  25, 54, 15, 17, 24, 9, 79, 98, -63, 44, 30, -73, -175, 68, -15, -11, -64,
  -5, 11, -57, 59, 14, -4, -30, -71, -79, 14, -25, -101, -26, -2, -12, 71]

theorem fractionalNearFrameSubtreeG5R0040_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0040Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0040Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0040Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0040_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0040LowerBoundTable : List ℤ :=
  [-38, 1, 1, 57, 32, 1, -62, 37, 97, 48, -55, -57, 99, 28, 172, -17, 134,
  268, 47, -44, 113, -37, -415, 77, 226]

def fractionalNearFrameSubtreeG5R0040LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0040Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0040LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
