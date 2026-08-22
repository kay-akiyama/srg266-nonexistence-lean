import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0275`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0275Mask : ℕ := 5371992843866792

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0275Witness : Array ℤ :=
  #[-131, 92, 86, -13, 33, 20, 72, 31, 0, 1, 94, 67, -9, -56, -48, 92, -31,
  91, 38, 22, 49, -4, 26, -15, -23, -55, 68, 0, -8, 14, -25, 57, 80, 49, 68,
  130, -46, -55, 51, 12, -57, 32, 83, -47, 68, -7, -19, -114, 24, -78, -84,
  20, -26, -43, -31, 3, -15, -127, 145, 97, 97, 90, -58, 103, 62, -87, -24,
  -74, -62, -59, -163, 78, 0, -50, 90, 14, -54, -58, 70, -30, 11, 46, -101,
  -25, -28, 51, 35, 23, -24, 2, 36, -9, 20, -43, 39, -6, -2, -1, -12, -5,
  42, -15, 81, 24, -36, 13, -28, -117, 15, 44, 44, 15, -42, -53, 50, -70,
  -49, -2, 201, 51, -126, -57, -11, -20, 0, 33, 14, 26, -116, 48, 121, 97,
  38, -5, 36, 71, 6, -13, 41, 56, -13, 6, 9, 101, -46, 111, 48, -43, -11,
  52, 3, 89, 58, 15, 139, 0, -190, 71, -17, 83, 54, 96, 9, 46, 20, 21, 53,
  95]

theorem fractionalNearFrameSubtreeG2R0275_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0275Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0275Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0275Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0275_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0275LowerBoundTable : List ℤ :=
  [55, 324, 97, 201, 129, 3, 26, 117, 2, 255, -12, 267, 15, 189, -22, 376,
  271, 344, 38, 566, 50, 100, 190, -149, 306]

def fractionalNearFrameSubtreeG2R0275LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0275Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0275LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
