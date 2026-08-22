import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0201`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0201Mask : ℕ := 6880035334738584

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0201Witness : Array ℤ :=
  #[11, 8, -3, 48, -3, -32, -39, -28, -66, -18, 41, 23, 52, 0, 16, -37, 10,
  20, -25, 12, -1, -2, 20, -35, 6, -5, 21, 13, -52, -2, -16, 19, 34, 6, 9,
  -14, 38, 18, 21, -18, -60, -6, -7, -26, 20, 18, 5, 8, 0, -14, 17, 39, 24,
  -10, 50, 6, -3, 24, -8, 3, 14, 6, 49, -20, 68, -58, -19, -17, -8, 22, -16,
  -19, -17, -35, -21, 32, -13, 7, -3, -46, -14, 4, 0, -18, -4, 58, 0, -15,
  8, -65, 26, 49, -40, -35, 31, 1, 9, 15, 0, 25, 14, -18, 11, 6, 11, 60,
  -16, -25, 65, 26, 42, 9, -15, -75, -9, -31, 4, 24, 33, -12, 13, 26, -6,
  17, -7, 46, -53, 28, -21, 31, -17, 4, -33, -1, 0, -33, -54, 23, 41, 16,
  35, 31, -18, 13, 21, 50, 0, 16, -35, 64, 20, -34, 26, 40, 17, -64, -12,
  -44, 5, -24, 33, -30, 13, -50, -23, 39, -73, 36]

theorem fractionalNearFrameSubtreeG3R0201_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0201Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0201Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0201Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0201_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0201LowerBoundTable : List ℤ :=
  [-26, 9, 12, 34, 34, -24, 2, 0, 8, 79, 105, 121, 228, 10, -3, 83, -107,
  -36, 100, 59, -50, 41, 52, 53, 70]

def fractionalNearFrameSubtreeG3R0201LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0201Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0201LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
