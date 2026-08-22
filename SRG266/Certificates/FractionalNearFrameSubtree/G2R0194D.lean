import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0194`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0194Mask : ℕ := 2330860113988611

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0194Witness : Array ℤ :=
  #[17, 47, -12, -44, -55, 0, 2, -63, -54, 0, 25, 26, 19, 20, 18, 24, 17,
  -9, -70, -47, -24, -91, -93, -59, 97, 40, 63, 79, 96, -14, -6, 5, 37, 0,
  33, 32, -24, -22, 12, 24, -48, -13, -12, 30, 30, 20, -1, -26, -41, -58,
  41, 16, -42, -37, 72, 62, 31, -5, -37, -57, 54, -27, 17, -14, 34, 11, -13,
  -1, -20, -19, -39, 22, -4, 8, 35, 15, 20, 13, 44, 43, -4, 68, 8, -14, 16,
  -7, 4, 93, 48, -27, 59, -3, 18, -28, 29, 6, 63, 61, 4, -14, 38, 16, -50,
  35, 20, 50, 26, 46, 69, 1, -66, -39, 7, 12, 8, 50, -39, 44, 45, 85, -50,
  -72, 14, 7, -34, 10, 6, -15, 43, -28, 30, 26, -7, -42, 11, 31, 47, -44,
  38, -2, 20, -110, -52, -16, -84, -57, 33, 46, -64, -14, -65, -1, 6, -14,
  36, -17, 37, -17, -3, -16, -17, 43, -87, -28, -1, -42, -35, -20]

theorem fractionalNearFrameSubtreeG2R0194_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0194Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0194Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0194Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0194_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0194LowerBoundTable : List ℤ :=
  [-49, -116, 59, 92, 3, 1, -22, 2, 79, 10, -26, 169, 57, 181, 158, 32, 92,
  60, 10, 103, 188, -56, 106, 21, -75]

def fractionalNearFrameSubtreeG2R0194LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0194Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0194LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
