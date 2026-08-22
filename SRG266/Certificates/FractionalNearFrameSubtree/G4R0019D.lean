import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0019Mask : ℕ := 4884765903268873

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0019Witness : Array ℤ :=
  #[78, 164, 109, 135, -28, -53, -78, -13, -36, -7, -55, 107, 20, 8, -31,
  -118, -117, -107, 0, -23, -72, 88, 16, -74, -33, -75, -45, 123, 127, 46,
  156, 97, 28, 96, 63, 108, -59, 28, 20, 41, -82, 89, 75, -25, -17, -65,
  -68, 54, 92, 123, 93, 74, 114, 64, 9, -69, 69, 67, 12, -56, -23, -42, -67,
  46, 7, -57, -80, 19, -63, -43, 83, 92, 71, 28, -74, 91, 20, -67, 70, 101,
  5, 42, 4, -2, -50, -107, -57, 22, 2, 31, -33, -4, -38, 43, 68, -21, 34,
  -72, -60, 22, -89, 19, 130, -36, 69, 183, 91, 6, -38, 7, -58, -66, -18,
  68, 93, -118, -69, -76, -6, 20, 60, 8, 0, -28, 47, 89, -150, 95, 50, 78,
  29, 122, 45, -7, 23, 67, 44, 74, -9, -21, 55, 44, 9, 115, 35, 44, -36,
  125, -14, 97, -1, -20, 42, 69, 32, -23, -173, 35, -12, 5, 20, -179, -19,
  55, 117, 30, -15, 136]

theorem fractionalNearFrameSubtreeG4R0019_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0019Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0019Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0019Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0019_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0019LowerBoundTable : List ℤ :=
  [91, 203, 30, 123, 219, -14, 287, 255, 218, 98, 297, 278, 150, 434, 292,
  265, 152, 251, 9, 224, -189, 438, 104, 196, 262]

def fractionalNearFrameSubtreeG4R0019LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0019Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0019LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
