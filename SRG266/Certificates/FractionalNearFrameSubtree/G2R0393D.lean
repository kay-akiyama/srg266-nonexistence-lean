import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0393`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0393Mask : ℕ := 5739970162541194

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0393Witness : Array ℤ :=
  #[117, 17, 121, 41, -31, 59, 0, 100, 10, 88, 124, -145, -106, -101, -156,
  -33, -12, 29, 86, 6, -11, 59, -25, -60, -59, -39, -1, 86, 49, 32, -67, 23,
  -22, 136, -62, 93, 75, 80, -59, -90, 8, 88, 56, -134, -115, 92, 39, 15,
  129, 82, -40, 57, -36, 21, 161, 44, 43, 77, 54, -108, -49, 84, -125, 15,
  -52, -76, 105, -3, -75, 37, 55, -177, -22, 24, -77, -44, 55, 116, 65, 68,
  91, -97, 124, -50, 83, 41, 12, -44, 29, 20, -8, -7, 96, 20, 42, 79, 38,
  82, -74, 135, 64, 83, 80, 86, -30, -115, -108, 20, -74, 15, -71, 149, 45,
  -24, 25, 21, 70, 72, -42, -101, 34, -35, -18, -37, -67, -81, 80, -135, 52,
  -83, 15, -58, 41, 11, 41, 66, 13, 27, -54, 126, -119, 92, -49, 42, -37,
  -65, 15, -94, -68, 51, -12, -79, -55, 51, 124, 153, 69, -33, -2, 39, 78,
  -70, 54, -19, -3, 19, 8, -17]

theorem fractionalNearFrameSubtreeG2R0393_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0393Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0393Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0393Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0393_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0393LowerBoundTable : List ℤ :=
  [23, -52, -12, 135, 78, 216, 65, 161, 2, 8, 11, 404, -157, 233, 161, 213,
  90, 165, 360, 385, -114, 176, 572, 395, 262]

def fractionalNearFrameSubtreeG2R0393LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0393Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0393LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
