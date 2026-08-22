import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0063`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0063Mask : ℕ := 969071478031498

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0063Witness : Array ℤ :=
  #[42, 33, -31, -10, 46, -3, 82, -12, -68, 50, -48, -14, 17, -63, -25, -25,
  25, -10, 35, -1, -1, 23, -31, -75, -134, -107, 39, 42, 10, 43, 29, 93, 14,
  24, -14, 1, -85, 78, -76, 44, -48, -21, 5, -44, 36, 44, -70, 0, -80, -29,
  47, 55, 30, 38, 20, -23, 18, 19, 51, -49, -165, -45, 72, 52, 73, -73, 39,
  18, 1, -27, -5, -8, 29, 4, 65, -86, 17, 83, 7, 12, 8, 6, 13, -1, 28, -45,
  -37, 69, -108, 14, -18, 38, 114, -56, -48, -17, -103, 27, -52, 42, -89,
  -4, 60, -33, -29, -22, -45, 69, -22, 19, -68, 38, -50, 0, -70, 29, -26,
  48, -34, -45, -223, 18, -40, 0, -55, -3, -33, -22, 30, 51, 145, -13, 3,
  -2, -9, 2, 33, -39, -18, -15, 120, 36, 79, -3, -165, 22, -24, 43, 49, 62,
  30, 25, -61, 30, -1, -58, -178, -65, 95, 93, -46, -9, 60, 84, 2, -14, -30,
  25]

theorem fractionalNearFrameSubtreeG3R0063_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0063Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0063Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0063Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0063_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0063LowerBoundTable : List ℤ :=
  [-118, 2, 1, -112, -71, -71, 2, 22, 1, -88, 51, 108, -231, 231, 123, 324,
  305, 59, -65, -147, -246, -271, -166, 90, 5]

def fractionalNearFrameSubtreeG3R0063LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0063Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0063LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
