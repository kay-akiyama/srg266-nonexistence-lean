import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0632`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0632Mask : ℕ := 11336972736761378

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0632Witness : Array ℤ :=
  #[-51, -153, -38, 69, 97, 169, -120, 277, 81, 118, 234, -287, -214, -115,
  -57, -130, 105, -101, 4, 231, -192, -4, 202, -81, 20, -155, -8, 46, -264,
  347, -80, 78, 248, 212, 115, -208, -212, -365, 248, 168, 192, -98, 0, 15,
  98, -49, 13, 76, 77, 98, 70, 209, -68, -154, 207, 39, 223, -141, -33, 90,
  -149, -21, 72, 197, -46, 0, 313, -153, 241, -62, -98, 2, -57, 106, 149,
  -85, 117, 137, -1, -3, 51, -75, -52, 235, -231, -255, -29, 117, -54, 101,
  19, 265, 12, 118, -117, -153, -150, -108, -63, -81, 16, -145, 330, 21,
  -325, -34, -72, -46, -24, -18, 130, -32, 0, 175, 47, 131, 201, 101, 37,
  -168, -89, 0, -160, 201, 49, 148, 80, 113, 31, 127, -45, -184, -108, 81,
  -69, 539, -12, 7, 77, 181, -14, 192, 25, 48, 215, 179, -83, -176, 21, 91,
  177, 117, 22, -30, 19, 28, 28, 180, -5, -91, 143, 71, 198, -112, -16, -10,
  112, -101]

theorem fractionalNearFrameSubtreeG2R0632_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0632Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0632Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0632Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0632_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0632LowerBoundTable : List ℤ :=
  [23, 551, 377, 244, 228, -41, 108, 1, 203, 649, 352, 516, 729, 806, 767,
  591, 611, 168, 10, 545, 516, 569, 371, -449, -153]

def fractionalNearFrameSubtreeG2R0632LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0632Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0632LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
