import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0021`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0021Mask : ℕ := 894576595933729

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0021Witness : Array ℤ :=
  #[144, -6, 16, 56, 4, -14, -55, -115, -28, -61, -70, -53, 26, -46, 14,
  -35, 30, -11, -85, 13, -60, -4, -6, 34, -24, -87, 12, -38, 10, 80, 69, 66,
  81, -60, -68, -57, 6, 42, 12, 28, 3, 19, -46, -66, 34, 17, 14, -21, -54,
  -70, -39, -31, 13, 0, 74, -147, 49, -8, 31, 38, -18, 1, 4, 18, -20, -83,
  110, -11, 18, 13, 9, 20, 22, -64, 46, 38, 23, 31, -35, -26, -9, -18, 22,
  -90, -7, 4, -17, 16, 19, 5, -9, 9, 29, -20, 8, -1, 74, 11, -38, 18, 44,
  57, -64, 31, -6, 8, -23, -41, -16, 15, -111, 30, -9, 76, -33, 11, 51, -32,
  -7, -16, 48, 43, -15, -12, -18, 16, 60, -9, 39, 24, 7, 26, 29, 9, 85, -7,
  29, 23, 42, 42, 6, -14, 32, 10, 21, 63, 70, 25, -38, 95, -15, 8, 74, -72,
  46, 49, 20, -59, -12, 68, -19, 73, -3, 25, -14, -47, -8, 0]

theorem fractionalNearFrameSubtreeG3R0021_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0021Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0021Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0021Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0021_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0021LowerBoundTable : List ℤ :=
  [-1, 168, 1, 162, 2, -37, 2, 45, -38, 269, -50, 9, 196, -91, 63, 84, -114,
  -21, -16, 56, 160, 11, 117, 10, 60]

def fractionalNearFrameSubtreeG3R0021LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0021Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0021LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
