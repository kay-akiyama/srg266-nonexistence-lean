import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0121`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0121Mask : ℕ := 1314583862817809

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0121Witness : Array ℤ :=
  #[-43, 0, 20, 62, 24, 105, -10, 33, 17, 68, 0, 20, 16, -49, -40, 5, -139,
  -75, -15, -9, -11, 3, 25, 38, -13, -9, -20, 7, 48, 70, 47, 54, -57, 17,
  -51, 18, 0, 7, 3, 20, 54, -3, 39, -65, 22, -1, 0, -17, 42, -24, -4, 18,
  40, -19, -2, 50, 10, -11, 125, -65, -5, -20, -5, -27, 38, -1, 29, 24, 15,
  -34, 6, -19, 4, -38, -13, 23, 24, 7, 95, 3, -11, -59, -52, 31, 19, 9, -22,
  35, -48, 31, -37, 38, -10, -30, 49, -8, 14, 15, 25, 0, -26, 1, 30, -50,
  -115, -55, -61, 59, 82, 20, 13, 41, -23, -69, -38, 15, -89, 12, 36, 7, 2,
  -23, 8, -23, -2, 62, -24, 16, -69, 35, -28, -18, 29, -22, 35, 47, -41, 0,
  4, -15, 4, -37, 22, -13, 18, 16, -36, 58, 6, -23, 39, -58, 84, -41, -30,
  -58, 8, -39, -56, 24, 4, 44, -34, 92, 42, 38, 30, -86]

theorem fractionalNearFrameSubtreeG2R0121_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0121Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0121Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0121Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0121_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0121LowerBoundTable : List ℤ :=
  [-16, 70, 2, 27, 2, 0, 58, 1, 18, 48, -55, 128, 19, -87, 58, -127, 48, 10,
  228, 76, -5, 134, 10, -43, 43]

def fractionalNearFrameSubtreeG2R0121LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0121Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0121LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
