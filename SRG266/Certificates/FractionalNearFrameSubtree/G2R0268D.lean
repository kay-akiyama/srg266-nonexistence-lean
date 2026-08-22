import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0268`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0268Mask : ℕ := 5369780332207256

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0268Witness : Array ℤ :=
  #[52, -18, 1, 5, -27, 18, 11, 2, 19, -33, 81, -27, 15, 28, 56, -2, -10,
  -10, 38, -22, -6, -22, -32, 36, 19, 18, 20, -2, 35, 41, -12, 67, 38, -18,
  -58, 81, 0, -45, 12, -67, 3, 52, -9, 58, -20, 27, -75, 25, 42, 3, -13, 60,
  30, 8, -17, 20, 33, 2, 24, -10, 45, -49, 21, -19, -10, -42, -14, 10, 61,
  28, 67, 41, 23, -14, -7, -53, 47, 32, -1, -1, 16, 0, -49, 38, 35, 45, -62,
  29, -72, -54, 30, -21, 0, 40, 29, -6, -33, -64, 20, 25, 15, 38, 54, 38,
  39, -31, 71, -24, 102, 19, 16, -70, -90, -33, -12, -47, 61, -39, 68, -47,
  -1, 46, 99, -44, -66, 70, 32, 24, -61, 40, 34, 33, 19, -23, 13, 1, 41, 41,
  58, -37, -59, 25, -3, 43, 16, -11, 27, 27, 52, 35, 16, 30, -39, -25, -55,
  -22, -54, 16, -51, 14, -19, 23, -27, 62, 11, 23, -58, -10]

theorem fractionalNearFrameSubtreeG2R0268_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0268Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0268Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0268Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0268_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0268LowerBoundTable : List ℤ :=
  [43, 52, 89, 73, 30, 28, 102, 136, 72, 8, 105, 162, -92, 11, 193, 81, 194,
  43, 21, 105, 67, 9, 311, 120, 203]

def fractionalNearFrameSubtreeG2R0268LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0268Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0268LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
