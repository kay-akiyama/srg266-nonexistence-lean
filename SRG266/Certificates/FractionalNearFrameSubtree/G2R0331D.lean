import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0331`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0331Mask : ℕ := 5638203119442441

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0331Witness : Array ℤ :=
  #[0, -15, -86, -44, -10, -121, -33, -56, -64, 44, -9, -143, 164, 86, 96,
  181, 116, 73, 35, 93, -9, 25, -15, 56, 30, 32, 6, -64, 14, 4, -28, -37,
  49, 14, -24, 28, -81, 53, 35, -2, 17, -17, 22, -81, 33, 80, 98, 56, 37, 5,
  -57, -39, -44, -97, -57, -42, -59, -48, -54, -33, 48, 50, 58, 72, -38,
  -27, 42, 13, -53, 17, 3, 22, 45, 17, 30, 55, 30, -33, -23, 53, 29, 39, 16,
  25, -2, -22, -23, -4, -19, 17, 18, -63, -28, -52, 18, -18, 28, 10, 15,
  -69, 71, 57, -85, 16, 3, 18, 35, 36, 27, 10, -80, 77, 67, 24, -69, 69,
  -11, 78, -2, -21, 38, 23, 26, -60, -48, -15, -5, -61, 8, -12, -32, 21,
  -34, 9, 5, -48, -35, -29, 70, 5, -59, 50, 82, -39, 51, 22, 62, -22, 5, 50,
  30, 68, 75, 32, 46, -17, -75, -18, -19, -36, -3, -4, 7, 16, 1, 34, 30, 37]

theorem fractionalNearFrameSubtreeG2R0331_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0331Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0331Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0331Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0331_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0331LowerBoundTable : List ℤ :=
  [24, 89, 2, 59, 89, 2, 2, 199, 157, 257, 120, 150, 11, 147, -14, -116,
  -83, 8, 136, 95, 100, 10, 234, -10, 189]

def fractionalNearFrameSubtreeG2R0331LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0331Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0331LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
