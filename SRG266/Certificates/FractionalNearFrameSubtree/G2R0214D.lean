import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0214`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0214Mask : ℕ := 2365766505536033

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0214Witness : Array ℤ :=
  #[-12, 24, 62, -44, 71, 78, -140, -36, 0, 3, 46, -17, -46, -42, 3, -33, 0,
  40, 52, 96, 97, 52, 4, -138, -161, 96, 9, 43, -43, -9, -87, 278, -50, 28,
  -192, -55, -51, 151, 65, 64, 36, 19, 51, -4, 171, -31, 25, -241, 5, -16,
  127, -2, 30, -28, 70, 29, -24, -42, -2, -85, -204, -1, -58, 111, 13, 52,
  -33, 62, -84, 59, 112, -15, -6, -49, -48, 85, -12, 43, -90, 46, 33, 57,
  71, -6, 39, 96, 24, 78, 219, 104, -10, -13, 15, 1, -15, -35, 42, 88, 15,
  -51, -2, 14, -60, -39, 10, -12, -50, 77, 126, -1, 144, 148, 127, 34, 103,
  103, 269, -78, -302, -141, -118, 35, 90, 49, 144, -39, 41, 64, 16, 1, 5,
  -30, -37, 0, -30, -42, 22, -59, -42, 36, -60, -9, -37, -69, -42, 11, -32,
  -50, -46, -10, -40, 18, -78, 8, 95, 31, 54, -39, -146, 40, -30, -22, -12,
  24, -31, -48, 119, -250]

theorem fractionalNearFrameSubtreeG2R0214_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0214Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0214Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0214Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0214_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0214LowerBoundTable : List ℤ :=
  [-12, -155, 48, 222, 53, 63, 122, 2, 2, -48, 136, 55, 98, 9, 155, 71, 105,
  217, 274, 322, 149, 101, 87, 375, -64]

def fractionalNearFrameSubtreeG2R0214LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0214Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0214LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
