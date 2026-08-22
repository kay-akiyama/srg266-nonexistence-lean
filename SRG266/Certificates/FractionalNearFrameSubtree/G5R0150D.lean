import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0150`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0150Mask : ℕ := 14250478783931666

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0150Witness : Array ℤ :=
  #[176, 125, 5, 80, 45, 27, 52, 18, -64, -50, -21, -132, -87, -48, -118,
  -54, 134, 65, -7, -25, -20, 97, 46, -80, -90, -16, 38, -10, -31, 22, 24,
  134, -40, -81, 116, -39, -43, -46, -50, -30, 75, -26, -10, -60, 84, -61,
  16, 100, 105, -28, -4, 45, 11, -14, -51, -23, -58, 85, 35, -19, 21, 4, 16,
  45, -8, -11, 16, 42, 2, 60, 69, 123, -17, 24, -83, 84, 105, 32, -34, 154,
  -67, -120, 15, 20, 5, 66, -36, -19, 77, 64, 113, 60, -87, 25, 58, -25, 39,
  43, 110, -22, -19, 33, 41, 149, -71, -58, -47, 21, -29, -54, -33, -32, 58,
  -43, -15, 0, -15, 41, -55, -118, -163, -145, 46, 54, 42, 65, 36, 142, -84,
  -30, -18, 37, 115, -22, 44, -62, -47, 57, -65, 3, 27, 39, -61, 157, 27,
  37, -55, 16, -53, 27, -24, -19, -5, -5, -10, -53, -60, 52, -28, 9, 40,
  -31, 0, -80, -56, 139, 56, 20]

theorem fractionalNearFrameSubtreeG5R0150_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0150Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0150Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0150Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0150_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0150LowerBoundTable : List ℤ :=
  [-8, 8, 43, -134, 228, 62, 212, -36, 143, -162, 42, -251, 103, 33, 234,
  415, 400, -44, 10, -26, 285, 10, 160, 205, 414]

def fractionalNearFrameSubtreeG5R0150LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0150Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0150LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
