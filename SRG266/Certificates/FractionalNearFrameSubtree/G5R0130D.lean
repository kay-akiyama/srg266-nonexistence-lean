import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0130`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0130Mask : ℕ := 5863474604706594

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0130Witness : Array ℤ :=
  #[-30, -11, 51, -17, -38, -19, -39, -19, -44, -44, -46, 89, 33, 23, 17,
  75, -10, -53, -13, 4, -52, 26, -19, 37, 32, -42, -7, 15, 30, 31, -50, -45,
  55, 8, 37, 6, 75, 0, -5, 6, -29, -15, -19, 17, -33, -10, -81, -36, -2,
  -12, 39, 76, 0, 25, 10, 11, -57, -50, -13, 30, -13, 16, 56, 4, -19, 1, 40,
  24, -40, 14, -64, 29, -78, 49, -52, -13, -50, -2, -19, 26, 11, -8, 36, 0,
  3, -11, 25, 11, 10, 36, 57, 25, 58, 64, 36, 1, -2, -22, -27, 94, 20, -4,
  46, 34, -65, 20, -22, 25, -35, -8, 7, -57, -19, -1, 21, 4, 22, -14, 1, -7,
  -71, 95, 25, 27, 36, 16, 33, -87, -1, -27, -2, -16, 2, -35, 16, -19, 38,
  -15, 29, 24, 1, 72, -49, 77, 36, 13, -41, 6, 41, 69, -7, -26, 0, -72,
  -122, 69, 60, -76, -77, 25, 0, -15, 0, 11, -58, 51, 34, -41]

theorem fractionalNearFrameSubtreeG5R0130_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0130Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0130Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0130Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0130_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0130LowerBoundTable : List ℤ :=
  [-33, 1, 2, 24, 26, 101, -21, -34, -10, -56, 74, 204, 24, -34, 140, -192,
  97, 23, 13, 63, 191, 38, 52, 64, 10]

def fractionalNearFrameSubtreeG5R0130LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0130Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0130LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
