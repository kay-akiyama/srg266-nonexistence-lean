import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0443`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0443Mask : ℕ := 5786370617554072

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0443Witness : Array ℤ :=
  #[7, 35, -21, 38, 76, 1, -25, 32, 14, -13, -78, 12, -45, -22, -42, -27,
  -7, -62, -32, 5, 12, 21, 12, 31, -44, 39, -13, 21, -25, 6, 34, 7, -19,
  -11, -4, 30, 20, 16, 0, 54, -16, 27, 21, 24, -10, -59, 26, -22, -5, 48,
  -3, -11, -5, 29, -70, -50, -28, 27, 30, 9, 30, -12, 24, -85, -16, -19, 34,
  -10, 5, 28, 8, 54, -7, -6, -1, -44, 38, -26, 38, 22, -9, 23, 65, -76, 31,
  -76, -31, -28, 30, 14, 12, -23, -51, 28, 63, 21, -31, 25, 17, -131, 0, 0,
  -46, 9, -15, 52, -7, -17, 104, 46, -12, 70, -50, 42, 17, 0, -36, 22, -18,
  3, 54, 15, 34, -17, 27, 63, 63, -21, -46, 48, 62, 18, -4, 12, -13, 8, 9,
  -49, 11, 3, -11, -79, -20, 18, -11, -33, -14, -47, 23, 40, -20, 55, 5, 48,
  30, 68, -58, 33, -108, 74, -19, -8, 27, 11, -12, 35, -4, -55]

theorem fractionalNearFrameSubtreeG2R0443_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0443Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0443Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0443Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0443_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0443LowerBoundTable : List ℤ :=
  [-45, 49, 1, -57, 38, -22, 2, 27, 36, 187, 159, 11, 223, 121, 151, 85, 36,
  74, 136, -84, 33, -53, 16, 9, 12]

def fractionalNearFrameSubtreeG2R0443LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0443Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0443LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
