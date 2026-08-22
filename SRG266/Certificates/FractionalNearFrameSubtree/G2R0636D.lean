import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0636`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0636Mask : ℕ := 11342101234521164

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0636Witness : Array ℤ :=
  #[-3, 35, 82, 242, 122, 34, -114, -20, 18, -1, -13, -232, -320, -168, -40,
  64, -40, -66, 72, 49, -39, -6, -111, -125, -76, 253, -75, -37, 43, 114,
  -16, -64, 51, -112, 76, 16, -145, 61, -37, 184, 26, 64, -2, -25, 13, 18,
  8, -5, 59, 194, -91, 146, -208, -31, 69, 127, -68, 78, -72, 94, -40, 17,
  -80, 109, -110, 61, 79, 37, 37, 193, -264, -153, 119, -117, 55, -33, 104,
  -74, -86, -4, 15, -149, -137, -61, 114, -12, 19, -206, -84, -50, -82, -64,
  45, 125, 43, -69, 82, -83, 43, -59, 43, 82, 147, -104, 55, 61, 111, 112,
  -94, 75, 89, 176, 237, 3, 13, -221, 81, 291, 209, 82, 112, 80, 49, 43,
  110, 152, 56, 32, 43, 22, -200, 162, 124, -14, 93, 184, 154, 239, 141, 47,
  10, -94, -250, 31, -122, -114, -133, 115, 106, -50, 41, 22, 150, 10, -9,
  139, -97, 158, 18, 9, -38, 228, -52, -18, 128, -23, -47, -153]

theorem fractionalNearFrameSubtreeG2R0636_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0636Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0636Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0636Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0636_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0636LowerBoundTable : List ℤ :=
  [-30, 341, 114, 192, 267, 55, -41, 2, 2, 966, 957, 1027, 333, 246, 102,
  183, 10, 568, -184, 182, 369, 10, -92, -151, 106]

def fractionalNearFrameSubtreeG2R0636LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0636Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0636LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
