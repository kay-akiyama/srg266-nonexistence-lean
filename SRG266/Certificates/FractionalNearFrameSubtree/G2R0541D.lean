import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0541`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0541Mask : ℕ := 6833355955538706

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0541Witness : Array ℤ :=
  #[54, 7, 44, 13, 117, -33, -54, 61, -52, 14, -85, 128, 21, -46, 64, -51,
  -14, -16, 5, 106, 26, 84, 53, -7, 36, -31, -35, -22, -101, -40, 39, 11, 0,
  34, -42, 115, -5, 22, 12, 46, 25, -47, 98, -33, 3, 38, 136, -8, 135, 9,
  -54, -77, 18, 72, -31, -73, -93, 81, -87, 0, 42, 6, -39, 121, -30, -60,
  -51, 32, -112, 57, -34, -40, 108, -15, 13, 42, 41, -70, 11, 19, -6, -79,
  5, 33, 0, -24, -53, -43, 20, 41, 68, -38, -46, 4, 16, 30, 40, 44, -78, 70,
  -89, 7, 36, -3, 42, -7, 93, 23, 2, -34, 12, -1, -60, 0, 40, 91, -61, 27,
  -23, 98, 28, -87, -12, 37, 112, -12, -68, -56, -46, -1, 13, 37, 86, 42,
  -15, 17, -11, -37, 75, -50, -26, -53, -4, 0, 25, -2, 6, 95, 54, 54, 101,
  13, -56, -65, 43, -90, -41, -40, -7, 13, -47, -48, 18, -18, 44, 77, -37,
  -45]

theorem fractionalNearFrameSubtreeG2R0541_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0541Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0541Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0541Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0541_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0541LowerBoundTable : List ℤ :=
  [30, 54, -43, -88, 105, 72, 2, 225, 123, 132, 107, 10, -191, 92, -121,
  210, 6, 43, 101, 50, 104, 391, 9, 43, 324]

def fractionalNearFrameSubtreeG2R0541LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0541Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0541LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
