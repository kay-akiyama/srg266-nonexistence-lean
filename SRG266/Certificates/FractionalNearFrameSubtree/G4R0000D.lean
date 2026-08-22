import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0000`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0000Mask : ℕ := 520939441717315

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0000Witness : Array ℤ :=
  #[-25, -34, -28, -70, -33, -68, 54, 48, 26, 10, -23, 2, 9, 16, -26, -48,
  -32, -82, -72, -29, -5, -73, 37, 23, -44, 13, -58, 65, 42, 40, 0, -12,
  -68, -35, -73, -37, -43, -35, 28, 48, 25, 9, 17, 42, -14, -32, 0, -47, -7,
  36, 21, 7, 13, -24, -3, -12, -22, 20, 33, -38, -7, 12, 18, 16, -13, 6, -7,
  22, 16, 30, 7, 26, 23, -1, 16, -32, -13, 13, 3, 7, 35, -23, -3, 3, 15, 17,
  9, 4, -7, -1, 32, -37, -38, 3, 3, 14, 25, 3, -29, 13, 25, 12, 19, 9, 27,
  0, -11, -12, -39, -57, -51, -60, -85, 40, 31, 42, -3, -16, 14, -36, -20,
  -2, 14, -54, -59, 0, -12, 29, 31, 63, -49, -58, -16, -7, -10, 36, -28, -9,
  41, 27, 26, -15, 2, 35, -6, 24, 25, -7, 48, 35, 27, 43, 20, 46, -44, -78,
  -24, -48, -10, -17, -18, -31, 2, 5, -7, 21, 28, 41]

theorem fractionalNearFrameSubtreeG4R0000_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0000Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0000Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0000Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0000_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0000LowerBoundTable : List ℤ :=
  [-95, 2, -62, -69, -33, 22, -25, 2, -7, 99, 19, 62, -79, 60, 80, -173,
  -133, 45, -165, -178, -142, -111, 9, 110, 12]

def fractionalNearFrameSubtreeG4R0000LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0000Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0000LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
