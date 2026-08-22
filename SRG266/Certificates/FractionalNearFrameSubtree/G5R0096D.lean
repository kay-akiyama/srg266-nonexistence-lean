import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0096`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0096Mask : ℕ := 5512178840474708

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0096Witness : Array ℤ :=
  #[119, 22, 133, 88, -8, 28, 6, -60, 115, 65, -31, 11, -104, -19, -48,
  -163, -28, -145, -4, -77, -36, -15, 97, 43, 110, 12, 48, -6, 43, 138, 3,
  88, 22, -27, -68, -96, -79, -19, -43, 54, -56, 7, 0, 36, 77, 18, -20, -40,
  -26, -146, 77, 53, -45, -82, -12, 114, 75, -8, -1, -31, -101, -129, 6, 58,
  -149, 0, 9, -140, 67, -47, 69, -26, 93, -88, 31, 55, -67, 50, 6, 30, 28,
  14, 24, 72, -181, -70, -11, 28, -54, -23, -104, 13, -13, -26, 27, -5, 36,
  -11, -42, -29, 11, 42, 75, -95, 69, -47, -71, 80, 92, 1, -17, -17, 139,
  84, 57, -26, -52, 91, 7, 91, 54, -46, -31, 152, 114, 35, 82, 103, 171,
  -17, 21, 55, 186, -25, 101, -63, 17, 106, -61, -62, -25, -109, 130, 19,
  -74, 72, 32, 118, 20, -13, 117, -52, 182, 11, -51, -53, 75, 15, 140, 81,
  -52, 104, -244, 44, -61, 114, 0, -153]

theorem fractionalNearFrameSubtreeG5R0096_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0096Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0096Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0096Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0096_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0096LowerBoundTable : List ℤ :=
  [-2, 272, -10, 1, 68, -172, 2, 123, 248, -197, 509, 221, 857, -26, 234,
  -279, 178, 221, 222, 194, 130, 329, -36, -42, 162]

def fractionalNearFrameSubtreeG5R0096LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0096Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0096LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
