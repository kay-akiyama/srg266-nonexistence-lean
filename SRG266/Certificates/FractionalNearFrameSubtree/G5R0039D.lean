import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0039`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0039Mask : ℕ := 1672660290863458

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0039Witness : Array ℤ :=
  #[52, 30, 39, 96, -79, 21, 19, -7, 42, -66, -36, 38, -40, -20, 0, -65, 50,
  -20, -15, 10, -151, 28, 67, -14, 8, -105, -15, -27, 90, -57, -11, 24, -50,
  51, 63, 41, 83, 15, 10, 32, 70, -56, -15, -111, -18, -22, -16, -12, 48,
  22, 48, 82, -66, 47, 69, -19, 14, 7, -35, -21, 52, 1, 19, 10, 27, 44, 0,
  -29, -99, 0, 11, -15, 31, 27, -30, -25, -54, 45, 101, -39, -42, -117, 62,
  67, 5, 38, -33, -166, 140, 58, 60, 139, -14, 44, 15, 4, -52, -44, -153, 2,
  33, 14, 0, 75, -10, -9, 49, -1, 6, 2, 1, -3, -4, -50, 3, -11, 43, 33, -81,
  9, 0, -12, -12, -52, -48, -38, 2, -43, 39, -16, -21, -12, -53, 71, -10,
  37, 63, -50, -5, -62, 29, 26, 0, 98, 80, -19, 45, -80, 26, -37, -14, -14,
  150, -17, 17, 40, -53, 73, 50, 8, -34, 24, 5, -28, 19, -58, 4, 14]

theorem fractionalNearFrameSubtreeG5R0039_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0039Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0039Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0039Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0039_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0039LowerBoundTable : List ℤ :=
  [-11, 8, 155, -19, -58, 44, 2, 57, 99, 122, -241, 39, 176, 124, 75, -223,
  278, 53, 198, 23, 18, 9, 81, -19, 72]

def fractionalNearFrameSubtreeG5R0039LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0039Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0039LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
