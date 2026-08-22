import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0478`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0478Mask : ℕ := 5810315159257490

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0478Witness : Array ℤ :=
  #[-65, -66, -42, 35, 61, 11, -11, 2, -25, 26, -102, -44, 76, 31, 20, -93,
  -19, -98, -16, -101, -19, -16, 81, -38, 33, -89, 41, 53, -4, 66, -3, 59,
  13, 41, -19, 38, 52, -135, -53, 63, 12, 100, -73, -32, -53, 116, 27, -127,
  -66, -3, 4, 18, 182, 132, -18, 58, 27, 5, 98, -17, 88, -40, 28, 9, 31,
  -25, -48, -24, -68, 42, -5, -11, -14, 66, 36, 58, 37, -46, 58, 3, 97, -24,
  -32, -61, 17, 43, -139, 34, -88, 99, -112, -35, 72, 10, -43, -52, 35, -30,
  33, 22, 54, 31, -59, 65, -21, 66, 30, 51, -70, 70, 4, 58, -46, -65, -18,
  -19, -85, 60, -27, -70, 141, -31, 22, 74, 45, -23, 79, -140, 41, 102, 13,
  29, -27, 63, 28, -106, -70, 51, 35, -135, 20, -25, 79, 100, 39, 52, 111,
  44, 80, 52, 57, -74, 47, -22, 13, 82, 3, -22, -75, -4, 3, 43, 37, -50, 57,
  -24, -112, -64]

theorem fractionalNearFrameSubtreeG2R0478_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0478Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0478Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0478Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0478_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0478LowerBoundTable : List ℤ :=
  [-43, 62, 2, 50, 63, 2, 36, 3, -22, 187, 137, 148, 266, 384, -80, 79, 58,
  10, 187, 216, 10, -10, 254, 107, 217]

def fractionalNearFrameSubtreeG2R0478LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0478Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0478LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
