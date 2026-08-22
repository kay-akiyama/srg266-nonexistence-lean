import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0185`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0185Mask : ℕ := 1388173572554992

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0185Witness : Array ℤ :=
  #[25, -16, 52, 38, -40, 28, 65, 47, 4, -31, -6, -28, -11, -47, 32, -75,
  38, -35, -61, 17, 53, 50, -25, -37, 46, 50, 17, 41, -18, -8, -57, -31, 51,
  -109, -38, 80, 125, 62, 93, -116, -62, -19, 61, -3, -97, -12, -49, 92, 57,
  9, 45, -31, 62, 112, 69, 32, 48, 31, -22, 8, -40, 6, -65, -36, -39, -23,
  -22, -3, 50, 13, -27, -20, -14, -55, -24, 48, 16, 8, 9, -10, -10, 28, -17,
  -9, 17, 18, 74, 64, -19, 22, 23, -2, -21, -8, 38, 51, 46, 55, 24, 13, 6,
  17, 34, -2, -32, -3, 4, -5, 39, -5, -27, 0, 40, 0, 22, 29, -13, 15, 32,
  -16, -6, -83, 6, 21, -35, -16, -35, -69, -63, 6, 10, -30, 37, -9, 85, 10,
  22, -34, 49, 17, -56, -2, 13, -31, 66, 32, 12, 34, -34, -40, -7, -26, 36,
  2, 61, -38, -18, -3, 42, 3, 33, -12, 1, -54, -62, 6, -4, 42]

theorem fractionalNearFrameSubtreeG2R0185_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0185Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0185Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0185Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0185_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0185LowerBoundTable : List ℤ :=
  [20, -23, 29, 53, 80, 100, 58, 46, 16, 39, -30, 10, -15, 15, 113, -38, 11,
  309, 248, 175, 104, -121, 168, 180, 93]

def fractionalNearFrameSubtreeG2R0185LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0185Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0185LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
