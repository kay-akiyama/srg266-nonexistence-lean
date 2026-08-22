import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0288`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0288Mask : ℕ := 5385118735377930

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0288Witness : Array ℤ :=
  #[-68, 80, -35, -56, 181, 57, 74, 147, 164, 154, 223, -142, -166, -59,
  -261, -18, -36, 22, 81, -76, 168, -97, 45, 43, -32, 49, 8, -42, -202, 53,
  87, 197, 166, -27, 52, 10, -119, -42, -127, 84, 165, 162, 329, 34, 80, 42,
  10, -124, 52, -28, -72, 59, 22, -43, 217, 398, 278, -142, -50, 93, -199,
  -181, 17, -88, 45, -26, -184, -159, 6, 2, 1, -75, 16, 55, 1, -181, 85, 24,
  36, 19, -11, 18, 110, 33, 80, -30, -16, -81, 17, -32, -116, -13, -119,
  -22, -173, -61, -108, -67, 57, 25, -34, 65, -12, -225, -21, -33, 17, -104,
  13, -46, -70, -63, 217, 17, 52, -28, -118, 44, -17, -51, 30, 99, 36, 67,
  5, 111, -8, -45, -197, 49, 26, 45, 10, 122, 210, -134, 80, 34, -7, 184,
  34, 95, 241, -79, 36, 214, -251, -118, 113, 205, 12, -40, -32, 245, 34,
  -24, -161, 115, 12, 180, -3, 72, -194, 141, 142, 24, 0, 48]

theorem fractionalNearFrameSubtreeG2R0288_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0288Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0288Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0288Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0288_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0288LowerBoundTable : List ℤ :=
  [88, 270, 326, 9, 1, 155, 262, -125, 1, 276, 575, 220, 557, 326, 254, -66,
  295, -176, -18, 1, 57, 116, 223, 461, 486]

def fractionalNearFrameSubtreeG2R0288LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0288Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0288LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
