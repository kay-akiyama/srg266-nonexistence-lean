import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0110`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0110Mask : ℕ := 1305924972036611

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0110Witness : Array ℤ :=
  #[114, 0, 30, 40, -57, 10, 0, -7, -266, -118, -178, -33, -3, 123, 236, 0,
  78, 76, 31, 94, 44, -57, 47, -99, 53, -66, -111, -59, -76, 99, 102, 20,
  -39, 168, 150, -49, 56, -57, -102, 133, 140, 92, -188, -137, 38, -206,
  370, -17, -41, -43, 106, -68, -91, -112, -14, 12, 103, 56, -105, 10, 117,
  30, 67, 56, -78, -41, -7, -81, 6, 86, 109, 139, 73, -1, 17, -55, 89, 61,
  -99, 12, -59, 50, 26, 45, 72, -114, -16, 38, -25, 106, 38, -36, 8, 0, 9,
  136, -41, -25, 114, 154, -170, 24, 7, 174, 51, 122, -20, 28, 176, -52,
  -79, -91, -5, -9, 38, 174, -50, 59, -24, 2, 95, -33, 109, 92, 32, -126,
  -162, 78, -40, 14, -18, 29, 114, 65, 0, 82, 35, 197, -116, 115, 152, -17,
  117, -50, -59, 31, 36, 25, 289, -22, 17, 27, 183, 16, -9, 87, -31, 25,
  -167, 104, -19, -84, -1, -164, 12, 139, -14, -126]

theorem fractionalNearFrameSubtreeG2R0110_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0110Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0110Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0110Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0110_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0110LowerBoundTable : List ℤ :=
  [85, 299, -4, 166, 1, 209, 228, 233, 107, 69, 272, 484, 247, 350, 380,
  322, 11, 283, 14, 98, 319, 351, -222, 472, 674]

def fractionalNearFrameSubtreeG2R0110LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0110Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0110LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
