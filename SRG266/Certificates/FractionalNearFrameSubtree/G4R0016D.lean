import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0016`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0016Mask : ℕ := 4877219205173509

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0016Witness : Array ℤ :=
  #[8, 20, -62, 21, 2, -3, -24, 74, -55, -19, -39, -19, 48, 31, 31, -8, -9,
  32, -11, 45, -4, -1, -24, 80, -20, 0, -30, -24, -60, 0, -15, 43, -10, -26,
  0, -5, 30, 16, 5, -35, -27, 49, 7, 15, -97, 61, 31, 0, 62, 39, -6, -2,
  -111, 136, -3, -98, -14, 34, -126, 20, 10, 24, 8, 2, -52, -38, 23, 124,
  25, -44, 27, 58, 45, 41, 85, -96, 10, -12, 16, -93, 9, -66, -34, 28, 29,
  26, -59, 57, 38, 2, -28, -19, -36, -36, -52, -4, 42, -24, -17, 10, -15,
  29, 5, 37, -20, -25, 63, -67, 12, -52, 23, 10, -9, -20, 21, -6, 34, 22, 4,
  44, 57, -32, -32, 12, -42, 60, -61, 31, -25, 50, 57, -81, -1, -51, -55,
  47, -34, -21, -26, 107, 19, 28, 14, -11, -2, -2, 44, 11, 54, 35, 4, 47,
  -105, -67, 2, 93, -82, 58, 68, -46, 23, -3, -37, 7, 42, -20, -25, 23]

theorem fractionalNearFrameSubtreeG4R0016_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0016Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0016Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0016Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0016_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0016LowerBoundTable : List ℤ :=
  [-51, 60, 3, 1, -70, 2, 89, 1, -25, 10, 218, 63, -177, 69, -66, 136, 226,
  10, 51, 206, 27, -185, 151, -48, 102]

def fractionalNearFrameSubtreeG4R0016LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0016Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0016LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
