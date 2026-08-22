import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0038`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0038Mask : ℕ := 1610891274461281

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0038Witness : Array ℤ :=
  #[62, 27, -8, -23, -81, -31, 137, 144, 141, 63, 70, -58, -17, -77, -99,
  -159, -17, -55, 18, -55, -80, 11, 26, 11, 89, 13, 22, 29, 100, 27, 79, 74,
  -59, 98, 14, 13, -37, -44, 52, 134, -9, -7, -27, -163, -116, 15, -107,
  -23, 110, 84, -21, -73, 44, 87, -67, -93, -19, 16, -27, -77, -24, 31, -93,
  -124, -10, 11, 8, -66, -43, -11, -17, 50, 4, -85, -23, -1, 89, 131, 24,
  28, -33, -57, 6, -34, -71, -22, -12, -102, -109, -42, 38, 96, 67, 23, 105,
  -14, -17, -2, 25, -39, -11, 88, 25, -42, -56, -8, 5, -21, -18, -45, 48,
  50, 3, 0, -6, 52, 6, 54, 44, 19, 52, -37, -46, 30, -68, 2, -63, -1, -25,
  -5, 12, -31, 13, 8, 0, -26, 76, -136, -155, 42, -113, 0, 16, -36, 30, -76,
  -26, 73, -31, 27, 18, 104, 16, 41, 4, 44, 1, -44, -70, -140, -34, 42, 46,
  -18, 39, 104, 67, 31]

theorem fractionalNearFrameSubtreeG5R0038_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0038Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0038Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0038Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0038_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0038LowerBoundTable : List ℤ :=
  [-85, -65, 2, -60, -44, 124, 2, -86, 2, -6, 204, -31, -281, 110, 10, -257,
  195, 67, 52, 69, -195, 154, -135, -88, 89]

def fractionalNearFrameSubtreeG5R0038LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0038Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0038LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
