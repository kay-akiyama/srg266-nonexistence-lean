import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0164`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0164Mask : ℕ := 1380069397185100

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0164Witness : Array ℤ :=
  #[-92, -97, 15, -84, -68, 39, 44, 20, 100, -21, 75, -15, 68, 43, 68, 30,
  51, -25, 123, -33, -60, 51, 76, 63, 83, -7, -10, -2, -40, -19, 29, -114,
  15, -72, 69, 45, -46, 38, 17, 85, 43, 20, -2, -7, -2, -88, -87, 26, 19,
  65, 58, 78, -10, -21, 16, 87, 51, 106, -27, 16, 89, -22, -107, -107, -30,
  26, 33, 11, -3, -50, -31, 75, -49, 4, 37, 0, -85, 42, 127, 63, 148, -73,
  -2, 36, 31, 9, 34, 65, -35, -32, 14, 41, 77, 39, -50, 51, -8, -18, 41,
  137, 78, 18, 49, 56, -49, -9, 26, -7, 36, 33, 16, -18, 81, 13, -2, -12, 0,
  60, 7, 47, -29, 7, 1, 4, -102, -40, 17, 30, -43, 30, 18, -15, 15, -3, -22,
  25, 16, 32, 84, -62, 51, -124, 89, 69, 54, 11, 44, -76, -20, 9, -23, 17,
  -2, -25, -4, 47, 2, 40, 21, -70, 8, -4, 17, -79, -24, 21, 6, 44]

theorem fractionalNearFrameSubtreeG2R0164_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0164Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0164Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0164Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0164_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0164LowerBoundTable : List ℤ :=
  [86, 31, 47, 143, 95, 144, 224, 181, 2, 187, 10, 216, -9, 101, 11, 40,
  107, 481, 363, 349, 80, 265, 10, 417, 124]

def fractionalNearFrameSubtreeG2R0164LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0164Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0164LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
