import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0202`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0202Mask : ℕ := 2346885726585347

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0202Witness : Array ℤ :=
  #[-89, -80, -101, -138, -135, -54, 48, -7, 2, -48, 0, 9, 54, 108, 200,
  174, 132, 160, 5, -18, 138, 14, 97, 154, 14, 0, 105, -1, 79, -111, -184,
  -18, -84, -42, 47, 135, -60, 26, -67, -12, 33, 24, 51, 62, 21, -25, 82,
  16, 27, -73, 100, -26, 68, 66, -56, -1, -5, -4, -29, -8, -75, 20, 87, 164,
  -37, -23, -5, 76, 44, -79, -70, 64, -65, 3, 74, -3, -121, 96, 36, 68, -17,
  87, 36, 35, 69, -15, -32, 23, -8, 66, -50, 96, -28, 8, 25, 125, 9, 69,
  -67, -10, -90, -89, -67, 16, 14, 25, -117, 51, 40, -28, -20, -71, -64, 12,
  -63, 76, 42, -27, 13, 44, -51, 58, -40, 48, -6, 45, -41, 54, 12, 5, -11,
  -24, 26, 36, 77, 22, -24, -50, 27, -1, 7, 89, 96, -5, 13, 10, 22, 53, 16,
  -20, 13, 14, -68, 142, 1, 7, 6, 34, 1, -23, 32, 20, 0, -39, -85, 7, -85,
  -22]

theorem fractionalNearFrameSubtreeG2R0202_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0202Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0202Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0202Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0202_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0202LowerBoundTable : List ℤ :=
  [54, 62, 27, 32, 2, 107, 219, 46, 179, 144, 188, -91, 115, 158, 367, 286,
  318, -156, 48, 46, 593, 9, 337, 279, 36]

def fractionalNearFrameSubtreeG2R0202LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0202Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0202LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
