import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0404`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0404Mask : ℕ := 5741420554695336

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0404Witness : Array ℤ :=
  #[85, 33, 20, 1, 70, -63, 74, -54, 46, -119, 21, 51, -29, 14, 42, -54, 25,
  -84, -19, -45, 20, 3, 60, 69, 51, 29, 6, -4, 137, 17, -24, -2, -51, -83,
  -52, 42, -33, -14, -4, -69, 11, -10, -46, -62, -82, 10, -24, 122, -22, 26,
  -11, 91, 136, -64, 95, 4, 52, -52, 47, -23, -32, -39, 70, -76, -144, -32,
  137, -39, 30, 0, 22, -29, 3, 98, 21, 71, -94, -77, -17, -2, 42, -4, 45, 9,
  38, -10, -1, 101, 27, -20, 70, 0, 13, -58, 98, 25, 48, 96, 96, 60, 41, -3,
  46, 64, 156, -32, 17, -40, 19, 47, 86, -23, 104, 8, 43, 1, -56, 11, 68,
  48, 36, 27, 79, -16, 25, -30, 8, 5, -22, -104, 129, -115, 45, 86, -23, 50,
  68, -17, -94, -20, -16, -54, -7, -83, -68, -20, 49, 54, -38, 123, 25, 31,
  64, 31, 115, -16, 50, -36, 35, -80, 38, 13, -57, -33, -69, -60, 23, -17]

theorem fractionalNearFrameSubtreeG2R0404_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0404Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0404Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0404Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0404_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0404LowerBoundTable : List ℤ :=
  [45, 54, 77, 241, 88, 38, 3, 97, 114, 239, -6, 211, -227, 533, 77, 9, 201,
  553, 160, 238, 399, 155, 10, -153, 271]

def fractionalNearFrameSubtreeG2R0404LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0404Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0404LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
