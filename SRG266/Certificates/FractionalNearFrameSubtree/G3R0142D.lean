import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0142`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0142Mask : ℕ := 6848284133626506

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0142Witness : Array ℤ :=
  #[-32, -51, 52, -36, 48, 35, -21, -24, 17, 59, -2, 19, 33, -48, 24, -16,
  -2, 3, -1, -46, 14, -27, 72, -57, 71, -33, -20, 73, 20, -11, -50, -5, 94,
  69, 19, 16, 2, -41, 50, -12, -35, -68, -10, -28, 54, 31, -6, 0, -49, -16,
  28, 82, -60, 12, 36, -51, -16, -20, -58, 22, -11, 9, -45, 44, -26, 78, 29,
  -7, 122, 9, -9, 25, -54, -46, -59, -25, -99, 28, 78, -21, 14, 42, 57, -67,
  -3, 27, -30, 23, -23, -58, -100, 52, -20, 53, -47, 21, -58, -26, 39, -38,
  -51, 68, -54, -71, 6, -27, -13, -7, 30, 1, 105, 53, -68, 26, -62, 10, 88,
  -26, -38, 18, 57, 110, -4, 13, -68, 12, 2, 25, 101, 142, 10, 58, -21, 25,
  -38, 12, -24, 28, 7, -27, 18, -90, -15, -22, -30, -34, -34, 39, -5, 48,
  -29, 52, -29, 98, 65, -17, 63, 75, 14, 57, -70, 41, -130, 90, 0, 0, 38,
  21]

theorem fractionalNearFrameSubtreeG3R0142_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0142Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0142Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0142Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0142_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0142LowerBoundTable : List ℤ :=
  [-29, 153, 1, 42, -8, 24, -29, 2, -54, 50, 182, 176, 10, 11, 348, 146,
  -46, -20, -9, -16, 442, 252, 176, 9, 11]

def fractionalNearFrameSubtreeG3R0142LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0142Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0142LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
