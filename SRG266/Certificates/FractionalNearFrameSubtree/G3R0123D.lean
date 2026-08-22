import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0123`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0123Mask : ℕ := 5402284644703384

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0123Witness : Array ℤ :=
  #[49, -45, 17, -51, -49, 72, 8, 52, 52, -20, 5, -1, -79, -51, 20, -50, 26,
  11, -11, 44, -13, 27, -98, 6, 2, 19, 31, -18, 95, -4, 0, 47, 27, -106,
  -85, 125, 31, 25, 2, -141, -57, -29, -38, -48, -34, 12, -72, 80, -54, 69,
  -15, 43, -33, -7, 62, 124, 56, 24, 42, -21, -12, 15, -85, -30, -15, 54,
  68, 76, -24, 46, -19, -3, -3, -87, -20, 7, -49, 22, -1, 30, -6, 30, 8, 59,
  10, 32, -87, 103, -136, -36, 15, -22, -113, -10, 78, -17, -7, -104, -30,
  1, -47, 44, 47, 0, 59, -44, -4, -34, -35, -33, 25, -43, -11, -64, 47, 35,
  -1, 20, 6, 33, 85, -98, 59, -14, -36, -24, 62, 43, 22, 2, 10, -135, -92,
  64, -42, 60, 92, 53, 49, 72, 36, -127, -136, 36, -18, -22, 38, 7, 30, -6,
  -21, 19, 9, 34, 18, 39, -67, 12, 38, -65, -107, -22, 100, -64, 69, 95, 0,
  0]

theorem fractionalNearFrameSubtreeG3R0123_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0123Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0123Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0123Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0123_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0123LowerBoundTable : List ℤ :=
  [-75, 3, 2, 1, -126, -47, 24, 38, 3, -178, 213, -108, 51, 105, 22, -164,
  220, -97, 64, 94, 119, 13, -47, 29, 323]

def fractionalNearFrameSubtreeG3R0123LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0123Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0123LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
