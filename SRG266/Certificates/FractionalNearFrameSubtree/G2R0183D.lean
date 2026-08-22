import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0183`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0183Mask : ℕ := 1388154648432880

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0183Witness : Array ℤ :=
  #[25, 47, 25, 15, 11, -8, -3, -29, -10, -39, 9, -3, -4, 3, -31, -8, -4,
  -2, -12, 6, -2, -14, 5, 0, 2, 40, 32, -7, -9, -8, 64, -1, 38, -11, -43,
  53, -20, -8, -2, -24, -10, -40, -17, 58, -26, -8, 12, 14, 56, -17, -18, 0,
  -38, 33, -25, 10, 12, -45, 68, 14, -31, -19, 22, -19, 23, -40, -20, 15,
  -43, -3, 47, 26, 46, -7, 70, -2, 36, 34, 17, -26, 15, -15, -18, -2, -44,
  -46, 1, -1, -19, -43, 17, -46, 12, -13, -36, 8, 11, -5, 66, -8, 27, -4,
  -21, -23, 18, -2, 10, -15, -27, -22, -31, -9, 28, 26, 21, -21, -10, -14,
  13, 17, 14, 52, 0, 11, -6, -15, -19, 1, 10, -19, 17, 9, 14, -4, 9, 20, 20,
  -12, -8, 11, 31, -17, -20, -35, 28, -1, -9, -9, 36, 20, -5, 49, 9, 9, 8,
  3, -18, -4, -4, -31, 3, -18, 42, 19, 24, -24, 44, 35]

theorem fractionalNearFrameSubtreeG2R0183_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0183Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0183Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0183Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0183_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0183LowerBoundTable : List ℤ :=
  [-37, 53, 11, -17, 56, -39, -3, -49, 68, 63, 16, 37, 51, 78, 8, 10, 117,
  120, 101, 9, 116, 182, 106, -41, 10]

def fractionalNearFrameSubtreeG2R0183LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0183Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0183LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
