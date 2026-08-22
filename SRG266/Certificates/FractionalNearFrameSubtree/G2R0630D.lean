import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0630`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0630Mask : ℕ := 11336474558842118

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0630Witness : Array ℤ :=
  #[-17, 28, 6, 6, -27, 96, 109, 101, 102, 90, 8, -122, -107, -72, -104,
  -47, -107, -41, -38, -102, 7, -28, 0, 46, -14, 38, -87, -27, 50, 71, 41,
  262, -14, 18, 18, 22, -42, -18, 72, 101, 31, 138, 19, 43, 27, 0, 74, 58,
  -16, 40, -23, -7, 44, 17, 128, -39, -33, -61, 5, 47, 5, -51, 37, -28, 63,
  32, 142, -75, 17, -134, 23, -47, -14, -7, 36, -14, 22, -24, 11, -59, -73,
  -12, -5, 2, 16, 61, 93, 29, 58, 110, 52, 57, 29, 51, 51, 55, -74, 7, 29,
  35, 104, -32, -31, 53, 2, -14, -72, 104, 50, -123, 21, 29, 41, 90, 61,
  -70, -19, 10, -23, 51, 13, 18, -45, 31, -9, -60, -7, -118, -21, 53, -34,
  -39, 1, -26, -11, 32, -161, -78, -40, -64, -20, 152, 83, 114, -18, 19,
  -22, 76, 2, 131, 14, 108, 0, 1, 96, -31, -47, 63, -48, 20, -133, -17, 32,
  97, 14, -110, -44, -182]

theorem fractionalNearFrameSubtreeG2R0630_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0630Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0630Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0630Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0630_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0630LowerBoundTable : List ℤ :=
  [20, 2, 44, 109, 3, 347, 94, 1, 0, 393, 22, 198, 44, 70, 221, 69, 77, 91,
  156, 29, 223, 55, 54, 452, 91]

def fractionalNearFrameSubtreeG2R0630LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0630Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0630LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
