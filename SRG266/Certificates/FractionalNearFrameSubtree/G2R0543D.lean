import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0543`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0543Mask : ℕ := 6833380571157650

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0543Witness : Array ℤ :=
  #[-47, 21, 4, -41, -38, 43, 5, 44, -25, -85, 1, 0, 8, 20, 15, 83, -8, -49,
  -31, -32, 15, -42, 39, 23, -68, -105, 27, 25, 67, 98, 25, -16, 56, 11, 20,
  3, -37, 1, 136, 20, -36, 14, 63, 8, -2, 55, -52, -12, 75, -20, 69, 16, 30,
  -65, 91, 52, -112, -49, -11, -41, -74, 26, 58, 114, -155, 21, -37, 47,
  -15, -53, -38, -33, 16, 16, -13, 31, -26, 38, 47, -19, 11, -29, 34, -50,
  50, -42, -48, 40, 23, -5, 25, -48, -33, 46, 7, -37, 23, 12, -75, 9, 46,
  14, 14, -99, -27, 0, 10, 8, 43, 20, 77, 36, -53, -80, 34, 61, 12, -27,
  -22, -32, 5, 37, 31, -16, 41, -35, -34, -124, -10, -4, -5, 99, -18, -43,
  13, 37, -31, 17, 9, -21, -3, -9, 100, 92, -28, -5, -68, 21, 35, -6, 12,
  52, 4, -17, 17, -61, 14, -22, -8, 35, 9, -46, -17, -35, -55, 16, 28, -3]

theorem fractionalNearFrameSubtreeG2R0543_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0543Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0543Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0543Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0543_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0543LowerBoundTable : List ℤ :=
  [-76, 2, 2, 3, 1, 2, 9, 0, 2, 75, 83, -28, 10, -2, 95, 164, 31, 60, 8, 11,
  259, -22, -114, 74, 143]

def fractionalNearFrameSubtreeG2R0543LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0543Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0543LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
