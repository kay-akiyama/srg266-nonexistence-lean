import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0599`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0599Mask : ℕ := 6868263477416560

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0599Witness : Array ℤ :=
  #[68, 64, 96, -84, 32, 128, 87, 84, 73, -116, -12, -72, 15, 29, 122, 6,
  47, -62, 140, 108, 28, -58, 35, 144, 19, -169, -79, -54, -43, 67, -48, 62,
  -57, 25, 0, 66, -7, 74, 41, 31, -123, -73, 40, 119, -128, 30, -57, 76, 23,
  85, 28, -55, -26, -74, 144, -10, -82, 86, -5, 12, -68, 41, 40, 21, -83,
  -8, 119, 89, 72, 38, -37, -1, -38, 113, -109, 125, 86, 91, 83, -148, -66,
  -1, -105, 90, 76, 20, 93, 87, 12, -38, -8, 47, -25, 57, 5, -176, 55, 87,
  90, 83, 50, 87, -133, 19, 113, 182, 71, -80, -138, -52, 15, 0, -78, -123,
  34, -88, 122, 142, 48, 77, -1, 25, -53, 40, 169, 18, 77, 94, 0, -46, -35,
  17, 37, 5, 15, 97, 54, 16, -32, 12, 50, -84, -28, -53, 66, -33, 34, 96,
  29, 29, 173, 41, 6, 80, 179, 106, 10, -17, -53, 20, -29, -19, -2, -1, -52,
  25, -68, 42]

theorem fractionalNearFrameSubtreeG2R0599_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0599Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0599Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0599Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0599_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0599LowerBoundTable : List ℤ :=
  [127, 294, -8, 120, 174, 149, 205, 282, 387, 69, 117, 562, 140, 393, -11,
  295, 98, 441, 11, 56, 433, -85, 829, 212, 396]

def fractionalNearFrameSubtreeG2R0599LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0599Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0599LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
