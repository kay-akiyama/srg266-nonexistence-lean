import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0009`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0009Mask : ℕ := 262426397171857

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0009Witness : Array ℤ :=
  #[175, 39, 108, 2, 87, -12, -41, -49, -70, 0, -75, -54, -10, -78, 32, -88,
  38, -78, -28, -79, 57, -49, -96, 55, -22, -8, 43, 41, 111, 27, 21, 29, 84,
  -72, -55, -110, -37, 120, 160, -58, -64, -69, -155, 189, 145, 34, 28, -39,
  9, 8, 8, -37, 34, -26, 5, -16, -83, -15, -33, -16, -67, -41, -3, -2, -11,
  3, 57, 62, 2, 62, 64, 31, -16, -12, -21, 31, 40, -7, 14, -3, 15, 8, -29,
  -73, 38, 7, 54, 81, 47, 20, 37, 52, 53, 134, -66, 40, 38, -15, -45, -1,
  10, -9, 29, 11, 37, 73, 47, 88, 28, 10, 26, 102, 14, -13, -28, -6, -92,
  -65, 10, 12, 46, -45, 44, -26, -20, -1, -6, -64, 60, -37, -12, -1, 20, 2,
  -20, 31, -4, 33, -16, -32, -60, 52, -4, -45, -65, 7, -7, -66, -116, 9,
  -103, 49, 10, -29, 34, -13, 34, 19, -40, 69, 58, 30, 51, 63, 56, -38, -39,
  0]

theorem fractionalNearFrameSubtreeG2R0009_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0009Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0009Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0009Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0009_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0009LowerBoundTable : List ℤ :=
  [-23, -49, 140, 1, 21, 2, 37, -65, 208, 180, -121, -45, 9, 215, 224, 220,
  43, 206, 212, 37, 166, -206, 299, 41, 11]

def fractionalNearFrameSubtreeG2R0009LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0009Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0009LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
