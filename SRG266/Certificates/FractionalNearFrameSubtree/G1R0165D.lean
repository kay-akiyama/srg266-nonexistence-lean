import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0165`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0165Mask : ℕ := 2368167021070609

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0165Witness : Array ℤ :=
  #[-121, -115, 0, -24, -41, -96, -215, -12, -37, -17, -49, -43, 63, 61, 39,
  125, 84, 143, 13, 35, 38, 77, 13, 36, -74, 23, -37, 0, -61, -20, -46, 82,
  -52, -21, 59, 43, 26, -21, -44, -23, -69, 15, -76, 61, 48, 43, 31, 1, -30,
  8, 1, 15, 14, 19, -23, -1, 45, 79, -55, 40, 0, -9, 12, -35, 16, -15, 16,
  60, -69, -21, 55, 3, -15, -42, 16, -6, 42, 26, 54, 2, -28, -34, -11, -12,
  16, -56, 14, 82, 25, 32, -6, -62, 3, -38, 18, -38, 0, -15, 82, -35, 81,
  -6, 7, -9, 21, 7, -21, 38, 17, -105, -63, 49, -32, 73, -5, 112, -8, 152,
  -100, -145, 38, 62, 51, 106, 75, 13, 29, -12, 52, -28, 65, 30, 53, -78,
  29, 31, 10, 47, 44, -28, 80, 82, 20, 33, 50, 44, 22, 48, 83, 13, 14, 25,
  7, 8, -21, 32, -39, -10, -37, -12, -63, -13, -84, 11, -1, -39, 40, -147]

theorem fractionalNearFrameSubtreeG1R0165_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0165Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0165Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0165Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0165_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0165LowerBoundTable : List ℤ :=
  [6, 104, 62, 125, 133, 3, 98, -113, -86, 263, 338, 155, 181, 20, -15, 50,
  23, 97, 167, 22, -75, 36, 9, 151, 149]

def fractionalNearFrameSubtreeG1R0165LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0165Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0165LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
