import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0641`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0641Mask : ℕ := 11403819646096902

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0641Witness : Array ℤ :=
  #[-27, 45, -1, 35, 62, -36, 113, 132, 93, 111, 138, -140, -85, -130, -227,
  -28, -150, -56, -92, -130, -142, 18, 66, 33, 61, 29, 93, 53, 143, 23, 61,
  110, 95, 59, -39, -58, 47, 108, -25, 36, 38, -15, 101, 42, 79, 75, 2, -21,
  -13, 86, -16, 54, 21, 5, -20, -9, -15, 12, 14, -10, -64, 48, 38, -130,
  -32, 130, -91, -9, 34, -86, 104, 47, -27, -33, -84, -22, 22, 36, -42, 25,
  11, -4, -41, 48, 31, 47, -69, -24, 94, 120, -36, 35, -76, 46, 25, 30, 64,
  -16, -16, 26, 69, 41, 46, 30, 21, 38, 70, 22, 68, 16, -36, 71, 60, 42, 17,
  -33, 36, 43, -70, 36, 98, 56, 122, -135, 38, -15, -34, -72, -5, -133, 4,
  60, 0, 7, 15, -87, -79, -28, 42, -43, -11, -15, -17, -8, -32, -59, 0, -40,
  6, -39, -42, -30, -48, 122, -23, 82, -94, 46, 0, 55, 70, -33, -38, 67,
  -10, -3, 0, -112]

theorem fractionalNearFrameSubtreeG2R0641_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0641Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0641Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0641Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0641_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0641LowerBoundTable : List ℤ :=
  [35, -77, 123, 1, 183, 161, -23, 155, 18, -17, 123, 151, -92, 141, 112,
  23, 55, 289, 226, 10, -70, 135, 306, 126, 444]

def fractionalNearFrameSubtreeG2R0641LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0641Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0641LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
