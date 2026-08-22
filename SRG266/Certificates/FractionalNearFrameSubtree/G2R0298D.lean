import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0298`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0298Mask : ℕ := 5387214776869080

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0298Witness : Array ℤ :=
  #[-175, -49, 0, 19, -45, 123, -9, -149, -15, 61, -107, 167, -72, 115,
  -170, 31, 69, 20, -85, 1, -60, 62, -39, 100, 36, -77, -95, 91, -42, 40,
  -131, -121, 38, 49, 88, -130, 67, 111, 103, 69, 0, 116, 165, -77, 94, -32,
  14, -73, 70, -26, -10, 10, -24, 42, 236, 167, -28, -216, 104, -158, -94,
  -98, 13, -119, 72, -140, -46, 36, 72, -44, -30, 37, -117, -23, 62, -86,
  -91, -35, 19, -53, 127, -64, -26, -67, -47, -3, -11, 163, -50, 71, -154,
  19, 109, 125, 165, -215, 0, -165, 107, -66, -83, 38, -6, -12, 154, -138,
  38, 20, 121, 150, 124, -67, 39, 85, -87, -39, -109, 93, -87, -9, -60,
  -141, 186, -43, 291, 124, -159, 33, 279, -51, 100, -67, 59, -78, 31, 24,
  12, 70, 194, 12, -19, -56, 27, 24, -59, 95, -21, 37, 110, -150, -42, 58,
  -94, 112, -9, -16, 56, 51, 49, -230, 36, -50, 45, 110, -76, -26, 66, -155]

theorem fractionalNearFrameSubtreeG2R0298_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0298Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0298Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0298Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0298_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0298LowerBoundTable : List ℤ :=
  [-42, 144, -2, 62, 133, -353, 92, -60, 91, 54, 246, 9, 388, 364, 274,
  -104, 506, 148, -361, -243, 286, 10, 534, -273, -238]

def fractionalNearFrameSubtreeG2R0298LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0298Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0298LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
