import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0028Mask : ℕ := 817540199563604

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0028Witness : Array ℤ :=
  #[9, 0, 20, 1, -13, 5, 247, 116, -55, -204, 126, -237, 70, 22, 26, -154,
  -116, 108, -108, 173, -13, -43, 77, -153, 63, -99, 10, -9, 274, -7, -48,
  153, 0, 144, -224, 85, 80, -88, -138, -189, -191, 202, 113, -111, 132,
  135, 169, 106, -78, -262, -278, -59, 65, 13, -200, -24, -240, 130, -24,
  59, -65, 42, -63, -91, 60, -12, 144, 84, -136, -1, 91, 29, 150, -306, 120,
  48, -86, -38, 237, 87, -149, -122, -3, -81, -299, 3, 39, -9, -173, 42,
  -229, -271, 63, 208, -71, 38, 229, -353, 177, -184, 127, -348, 14, 33, 26,
  43, 100, -180, 195, 325, -91, -37, 135, 125, -21, -101, 157, 71, -227,
  194, -147, 246, 21, -82, 212, -202, 104, 97, 49, 143, 117, 92, 114, 249,
  58, 175, 124, -176, 281, 194, 144, -66, 153, 57, 267, 53, 146, 59, 422,
  -188, 115, 33, 198, -37, 243, -49, 165, 28, -95, 136, -395, 388, 26, -63,
  161, -84, 131, 3]

theorem fractionalNearFrameSubtreeG2R0028_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0028Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0028Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0028Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0028_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0028LowerBoundTable : List ℤ :=
  [65, 675, 171, 225, 177, 2, 69, 2, 108, 906, 773, 1009, 1033, 324, 8, 289,
  -220, 423, -199, 9, 27, 270, 222, -822, 307]

def fractionalNearFrameSubtreeG2R0028LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0028Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0028LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
