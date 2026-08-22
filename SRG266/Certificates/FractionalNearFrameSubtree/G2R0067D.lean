import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0067Mask : ℕ := 954155586782290

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0067Witness : Array ℤ :=
  #[77, 13, -41, 134, -16, 101, -29, 1, 14, -55, 5, -48, 21, -14, -34, -21,
  2, 17, 40, 55, -14, 33, 6, 13, -14, -57, -51, 16, -19, -38, -6, -69, 95,
  -29, 85, 0, -54, 50, 25, -45, -23, 3, 20, 0, 22, -9, -63, -30, 24, -15,
  77, 68, -17, -8, -66, -2, 77, -49, 33, -11, -21, 51, -24, -40, 19, -57,
  17, 36, 16, 38, -12, 72, 23, 6, 26, -50, 14, -30, -6, -52, -8, -10, -50,
  -37, 4, 27, -62, 23, -12, 22, 2, 26, 65, -12, -88, 75, -53, 50, -80, 35,
  53, -56, -95, 72, 15, -2, -12, -51, 28, 95, 23, 84, 7, -57, 11, 58, 21,
  -4, -33, 0, -15, -57, 37, 38, 18, 69, 31, -35, -4, 17, -45, 0, 14, -12,
  -38, -76, 43, -67, 47, -26, -4, 64, 7, 72, -27, 92, -25, -26, -17, 9, 54,
  -30, 21, 65, -55, -43, -26, 18, 14, 5, 8, 17, 27, -61, 24, 69, -64, -39]

theorem fractionalNearFrameSubtreeG2R0067_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0067Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0067Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0067Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0067_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0067LowerBoundTable : List ℤ :=
  [-7, 37, -32, -17, 25, 44, 71, 131, 1, -45, -73, -21, 166, 10, 33, 109, 9,
  -109, 34, 128, -27, 10, 147, -47, 240]

def fractionalNearFrameSubtreeG2R0067LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0067Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0067LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
