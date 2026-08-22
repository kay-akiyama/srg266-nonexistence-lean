import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0406`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0406Mask : ℕ := 5742488192649584

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0406Witness : Array ℤ :=
  #[-4, 12, 83, 6, 15, 16, -15, 2, -19, 17, -12, 26, 22, -26, -43, 16, 1,
  -32, 78, 32, 39, -51, -42, 17, -7, 88, 27, -6, -26, 9, -34, -73, 40, 53,
  36, 14, -22, 42, 0, 16, 43, -46, 3, 67, 0, -9, -15, -5, 31, -42, -21, -4,
  3, 14, -24, 81, 16, -10, -15, 65, 56, 21, -61, -52, 16, -19, -117, 13,
  -110, -30, 0, -23, 23, -31, 4, 8, -62, 25, 52, 14, -35, -47, -74, -15, -5,
  -67, -13, -33, 4, -71, 44, -9, -7, -14, 22, -6, 12, 21, -32, 22, 26, 17,
  19, -29, 29, 32, 94, 25, 9, 47, 30, -27, -44, -47, -36, -59, -12, 20, -9,
  -9, 58, -29, 26, -1, -52, -26, -3, 37, 3, -39, -45, 3, 19, -2, 8, 32, 24,
  24, 65, 70, 50, -26, 22, 0, 33, -16, 20, -39, 44, -120, 33, -8, 41, -42,
  31, 14, 32, -42, 106, -1, 22, -5, -96, -16, -19, 63, 28, 18]

theorem fractionalNearFrameSubtreeG2R0406_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0406Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0406Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0406Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0406_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0406LowerBoundTable : List ℤ :=
  [-67, 1, 19, 52, 23, 1, 1, -17, 56, 205, 119, -61, 5, 120, -104, -215,
  355, -50, 98, 10, 15, 158, 59, 9, -39]

def fractionalNearFrameSubtreeG2R0406LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0406Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0406LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
