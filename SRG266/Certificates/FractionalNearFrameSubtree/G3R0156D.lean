import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0156`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0156Mask : ℕ := 6850430498938392

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0156Witness : Array ℤ :=
  #[-4, 54, 42, -95, 146, 22, -12, -167, 182, -87, 46, 34, -67, -137, 72,
  -69, -169, -136, -113, 80, 65, -116, 205, 239, -112, -31, -108, -55, -87,
  -63, -52, -60, 1, -77, 122, 119, 58, 39, -100, -64, 148, 27, 36, 1, -7,
  -47, -159, -17, 46, 61, -14, -6, 6, 30, 33, 98, -8, -22, 59, -2, -8, 109,
  -129, -37, 40, -24, 53, -25, 6, 59, 73, 177, 64, 129, 9, 91, 24, -81, -24,
  147, 57, -19, 149, -15, 44, -43, -27, 138, 0, 186, 66, 80, -48, -21, 55,
  -16, -52, -67, -48, 86, 91, -2, 54, -29, 2, 65, -144, 29, -15, 83, -40, 5,
  -139, 140, 17, -296, 55, -14, -90, -27, -48, -103, 134, 183, 72, 143, -62,
  236, -166, 26, -124, -17, 8, -39, -37, -11, 79, -123, -39, -57, -54, -61,
  25, -20, -75, -28, -15, 125, 56, 156, 220, -54, 147, 83, -150, 135, 175,
  -139, 127, -30, 85, 85, -136, 115, 131, 188, 153, 78]

theorem fractionalNearFrameSubtreeG3R0156_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0156Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0156Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0156Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0156_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0156LowerBoundTable : List ℤ :=
  [45, 289, 559, 104, -91, 141, 35, 67, 80, -98, 208, 134, 181, 355, 229,
  431, 277, 10, 644, -3, -502, 388, -58, 11, 585]

def fractionalNearFrameSubtreeG3R0156LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0156Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0156LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
