import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0014`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0014Mask : ℕ := 760430003395089

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0014Witness : Array ℤ :=
  #[-46, -39, -57, -80, -85, -115, 83, 26, 66, -41, 22, -4, 81, 5, 60, 34,
  -11, 1, -68, -49, -38, 11, -6, 68, 18, 13, 21, 23, 3, -6, -39, -39, -54,
  -45, -37, 23, -3, 76, 10, 2, 9, -12, 11, 27, -43, -33, -6, -11, 86, 13,
  -11, 15, 31, 0, 15, 9, -7, 12, -13, 108, 4, -10, 15, 21, 21, 11, 30, -30,
  46, -4, 0, 37, -21, 18, 13, -36, -28, -10, -20, 13, -42, -14, -49, -8,
  -53, -16, 0, -1, -6, -48, -31, 22, -9, 6, -27, 10, 11, -69, -18, 76, -59,
  54, -37, 0, 9, -80, -129, -91, -56, -86, -54, -78, -49, 161, 178, -34, 0,
  38, 20, 17, 41, -12, 31, -36, -4, 13, 0, 33, 43, 21, 12, 38, -15, 14, -33,
  -80, 27, 18, 12, 52, -21, 36, 76, 48, 47, 42, 18, -13, -3, 18, 11, 4, -6,
  -11, 21, 15, 7, -43, 30, 63, 10, 0, -15, -38, -20, 56, -19, -9]

theorem fractionalNearFrameSubtreeG3R0014_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0014Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0014Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0014Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0014_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0014LowerBoundTable : List ℤ :=
  [-41, 85, -45, -24, 1, 32, -39, 1, 55, 87, 72, 75, 12, 111, -108, -54,
  -128, 173, -44, -49, -144, 7, 9, 17, 81]

def fractionalNearFrameSubtreeG3R0014LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0014Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0014LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
