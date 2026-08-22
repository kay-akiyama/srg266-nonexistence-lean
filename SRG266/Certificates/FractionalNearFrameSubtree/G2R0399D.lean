import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0399`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0399Mask : ℕ := 5740382328398242

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0399Witness : Array ℤ :=
  #[-27, 0, 20, 54, 6, -2, 0, 49, 60, 44, -11, -40, -68, 38, 31, -24, -8,
  29, -16, -76, -32, -30, 88, -31, 7, -73, 66, 40, 72, 48, -40, 11, 15, -34,
  73, 38, -19, 40, 34, 23, 37, 12, 4, -13, 19, 36, -71, -84, -33, 70, 109,
  10, 76, -60, -23, -25, 0, -6, -50, 51, 19, 41, 24, 25, 35, -29, 10, -7,
  29, -30, -47, 49, 18, 66, 48, 23, -25, 60, 26, 18, 15, -31, -24, 48, -20,
  13, 32, 29, -53, 17, -20, -40, -50, 58, 0, 14, 9, 19, -8, 31, -101, 58,
  -74, 13, 50, 51, 46, 3, -39, -46, -40, -30, 6, 45, 14, -4, 20, 11, 25, 58,
  71, -22, 84, -37, 8, -29, 1, 21, 50, 33, 35, -20, 67, 20, 47, 30, -51, 51,
  7, 41, -30, 58, -5, 4, 51, 54, -52, -2, 37, 57, -59, 55, 29, -19, 2, -28,
  64, 28, -95, -41, 27, 6, 19, 38, -34, 34, -30, 44]

theorem fractionalNearFrameSubtreeG2R0399_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0399Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0399Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0399Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0399_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0399LowerBoundTable : List ℤ :=
  [53, 113, 114, 118, 2, 85, 61, 57, 140, 224, 270, 107, 403, 10, 114, 154,
  9, -181, 68, 256, 256, 136, 121, 261, 252]

def fractionalNearFrameSubtreeG2R0399LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0399Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0399LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
