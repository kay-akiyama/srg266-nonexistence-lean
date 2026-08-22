import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0589`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0589Mask : ℕ := 6862832059499146

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0589Witness : Array ℤ :=
  #[-38, 2, -44, 47, 7, 30, -15, -8, -48, 0, 19, -24, 21, -14, -10, 34, 18,
  -33, 38, -12, 56, -53, -37, 22, -18, 35, -36, 0, 1, 48, -32, 53, -19, -34,
  -44, 44, 11, 2, 79, 23, 52, -58, -8, 38, 33, 44, -84, -75, 52, 46, 51, 5,
  -19, 1, -42, -39, 51, -57, 63, 48, 9, -2, -69, 54, -40, -18, 3, -3, -2,
  62, -21, 23, 44, 28, 30, -26, 14, -63, 24, -55, 40, -43, 25, -43, -3, 27,
  22, -32, -16, -11, -6, -25, -52, 24, -10, 97, -46, 82, -52, 7, -64, -27,
  -41, 40, -21, 8, 6, 38, -49, 15, -19, -4, 42, 33, -98, -23, -43, -14, 39,
  21, 48, -3, -32, -45, 73, 68, -38, 67, 0, 13, -42, -10, -42, 48, -19, 6,
  -16, 32, 18, -12, 58, 9, -36, -33, -5, -5, -14, 0, -42, 18, -73, 20, -23,
  2, 21, 13, 24, -40, 16, 9, -6, 10, 24, -43, 48, 3, -70, -35]

theorem fractionalNearFrameSubtreeG2R0589_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0589Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0589Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0589Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0589_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0589LowerBoundTable : List ℤ :=
  [-74, 2, -45, 1, -47, 1, 1, 1, -32, 84, -88, -39, 58, 10, 98, -123, 222,
  19, 74, 41, 33, 63, 10, 139, 47]

def fractionalNearFrameSubtreeG2R0589LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0589Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0589LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
