import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0108`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0108Mask : ℕ := 5791991545628753

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0108Witness : Array ℤ :=
  #[-1, -2, 42, 46, 14, 16, -12, 71, -13, -32, 24, 0, -20, -21, -59, -48, 7,
  -8, -26, -14, 17, 13, 24, 18, 83, -22, -27, 42, -46, 33, -20, 13, 3, -18,
  -18, 0, 15, 21, 14, 70, -15, -61, -70, 26, 58, -1, -19, 9, -67, 55, -18,
  17, -30, 19, -37, 6, -8, -14, -4, 15, 5, 34, -25, -26, 28, -35, 33, -6,
  -37, 15, 4, 30, -59, 36, -37, -20, -64, 30, 18, 14, -23, -35, -19, 68, 26,
  -34, -9, 3, 3, 64, 29, 29, -44, -41, 90, 17, 40, -28, -29, -25, 57, 46,
  -18, -10, 38, -12, -37, 3, 8, 66, 40, 8, -53, -9, 3, 35, -38, 21, 22, -32,
  1, 32, 9, -4, -2, -60, 48, -33, 66, 83, -13, -26, -90, -49, -16, 17, -59,
  30, 43, 96, -13, 63, 45, -47, 31, 15, 0, -32, -63, 18, 37, 37, -35, 31,
  -29, 46, 26, 56, -25, 21, 25, 43, 37, -70, 8, 24, 76, 33]

theorem fractionalNearFrameSubtreeG5R0108_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0108Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0108Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0108Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0108_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0108LowerBoundTable : List ℤ :=
  [-5, 79, 1, 91, 48, 120, -32, -51, 26, 167, 10, 55, -55, 197, 226, -34,
  -18, 123, 114, 45, 156, 34, 122, 257, -124]

def fractionalNearFrameSubtreeG5R0108LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0108Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0108LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
