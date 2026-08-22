import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0161`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0161Mask : ℕ := 1379523374203554

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0161Witness : Array ℤ :=
  #[33, 33, 36, 26, 28, 61, -17, -30, -13, -37, -27, -51, 8, -54, -20, -100,
  -34, -11, -31, -65, -19, 8, 28, -15, -34, -18, 39, 12, 19, 62, -64, 10,
  17, 19, 8, 21, 2, -7, 13, 1, 22, 16, -71, -2, 24, 11, 23, 36, 41, 41, -28,
  2, -24, 44, -39, -82, -47, 22, 20, 57, 53, 0, 45, 36, 6, -27, -45, 17,
  -23, -17, 31, 10, -2, 4, 28, 37, 46, -23, 60, 2, 6, 3, -7, -22, 19, -25,
  37, -22, 49, 6, -13, 20, -23, -7, 7, -39, 15, -28, 22, -26, -48, -38, -32,
  -43, 1, -51, -20, 8, 8, 25, 11, -8, -35, -12, 4, 6, 16, 1, 0, 20, -31, 28,
  -30, -30, -15, -33, 9, 23, -17, -69, -57, 8, 3, 36, -20, 31, -47, -6, -19,
  -27, 31, 4, 42, 5, 18, 36, -43, 5, 19, -8, 5, -34, 35, 25, 20, 33, 32,
  -11, -9, 32, 17, 25, 23, -7, 44, 6, 25, -69]

theorem fractionalNearFrameSubtreeG2R0161_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0161Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0161Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0161Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0161_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0161LowerBoundTable : List ℤ :=
  [-42, 2, 12, -92, 11, 25, 12, 18, 2, 53, -5, 125, -66, 10, -97, 9, 31,
  -52, -77, -6, -24, -16, 199, 101, 73]

def fractionalNearFrameSubtreeG2R0161LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0161Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0161LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
