import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0188`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0188Mask : ℕ := 6866717027022348

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0188Witness : Array ℤ :=
  #[-91, -39, 122, -88, -11, -14, -91, -77, -57, -52, -36, 42, 67, 56, 68,
  151, -91, -54, -109, 20, -10, 61, -11, 112, 3, 5, 71, 47, 112, -23, 10,
  -5, 8, -16, 26, 50, -32, 14, 19, 18, 59, 5, 89, 5, 82, -49, 8, -35, 11,
  -9, -52, 10, 1, 61, 113, 128, 11, -12, 36, -112, -55, 89, -70, -20, -106,
  -10, 0, -45, -17, -35, 45, 20, 63, 65, 9, 23, 8, 56, 94, -53, -66, -8,
  -25, -67, -7, -34, -71, -53, -24, -62, -10, 17, -48, -46, -9, 11, 2, 8,
  44, 14, -13, -39, 74, 2, -13, 54, 85, 2, -37, 93, 65, 1, 39, -53, 41, 40,
  7, -25, -55, -3, 57, 14, 74, 74, 42, 15, 43, 30, 20, 61, 22, -34, -49, 96,
  -32, 78, 62, 38, 57, 59, 76, 19, 58, 72, 66, 62, -19, 25, 121, 41, 108,
  -29, 83, 61, -78, 1, 21, -69, -22, -19, -57, -16, -69, 12, 63, -66, -82,
  -36]

theorem fractionalNearFrameSubtreeG3R0188_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0188Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0188Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0188Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0188_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0188LowerBoundTable : List ℤ :=
  [89, 216, 2, 103, 87, 185, -122, 135, 103, 656, 181, 166, 298, 10, 49, 73,
  -10, 12, -18, 279, 78, 37, 10, 10, 394]

def fractionalNearFrameSubtreeG3R0188LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0188Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0188LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
