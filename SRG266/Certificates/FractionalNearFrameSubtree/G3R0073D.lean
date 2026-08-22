import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0073`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0073Mask : ℕ := 2339550495611921

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0073Witness : Array ℤ :=
  #[-52, 13, -5, -143, 27, -16, 25, 101, 56, -6, 2, 63, 30, -98, -163, -40,
  -76, 0, -44, 12, -9, -38, -50, 80, -28, 50, 18, -82, -91, -51, -14, 232,
  52, 33, 75, -74, 7, -103, -68, -60, 173, -2, 107, 28, -282, 71, 45, 24,
  -26, 69, 139, 12, -1, -78, -4, 147, -72, -34, 4, 30, 112, 87, -14, -90,
  22, 66, -7, 25, -28, -82, 148, -86, 34, 19, 118, -67, 7, 50, 151, 53, 51,
  -10, -9, 52, -95, 83, 177, -65, 42, -16, 65, 22, 30, 136, -76, -48, -209,
  54, 24, 27, -89, 60, -24, 84, -105, -93, -79, -89, -33, -28, 33, -62, 125,
  -1, 156, -48, -21, 86, 131, 56, -68, 40, -95, 193, -26, 88, 108, -17, 11,
  59, 90, -59, -26, 129, 5, 8, -176, 40, 20, -30, 123, 154, 56, 108, 41, 61,
  34, -164, -97, 52, -3, 13, -74, 40, 10, 34, -2, 69, 36, -27, -3, 100, 20,
  -2, -116, 84, 16, 128]

theorem fractionalNearFrameSubtreeG3R0073_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0073Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0073Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0073Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0073_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0073LowerBoundTable : List ℤ :=
  [32, 223, 37, 301, -5, 103, 196, 1, 31, 272, 312, 69, 244, 44, 230, 107,
  65, 356, 185, 278, 294, -53, 10, 414, -221]

def fractionalNearFrameSubtreeG3R0073LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0073Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0073LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
