import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0177`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0177Mask : ℕ := 6865884883653778

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0177Witness : Array ℤ :=
  #[38, 4, 62, -10, -21, 20, -35, 3, 8, -12, 0, -13, -56, -34, -58, -27,
  -29, -57, -67, -63, -73, -39, 43, 65, -4, -23, 42, 61, -43, 118, 61, 27,
  49, 16, 65, -29, -61, -2, 5, 10, -51, 0, 51, 66, -6, 7, 15, -4, 35, 51,
  -1, -2, -8, 126, 61, 11, -39, -51, 4, -30, -22, 31, 89, 65, -141, 30, -13,
  23, -63, 6, -3, 47, -55, -13, -28, -63, -48, 29, 16, 3, 47, 73, -5, 22,
  -9, 77, 19, 16, -13, -1, 29, -11, 31, 63, 34, 51, -29, 48, 33, 22, 22, 43,
  10, 57, 17, 66, -101, -30, 0, 1, 22, -51, 89, 26, 47, -18, -36, -8, -10,
  -11, 42, 6, 102, -89, 35, 0, -36, -55, -70, 1, -50, 136, 60, -52, -18,
  -54, -25, -7, -18, 2, 12, 48, 12, 27, 20, 46, 66, 37, -74, 4, 22, 19, -17,
  27, 17, 30, 0, 47, -45, -13, -3, 104, -35, 28, 40, 85, 2, -44]

theorem fractionalNearFrameSubtreeG3R0177_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0177Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0177Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0177Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0177_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0177LowerBoundTable : List ℤ :=
  [26, 103, 162, 2, 107, 94, 1, 84, 7, 65, 11, 114, 113, 211, 263, 43, 140,
  37, 9, 84, 269, 129, 170, 8, 10]

def fractionalNearFrameSubtreeG3R0177LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0177Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0177LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
