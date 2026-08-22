import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0082`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0082Mask : ℕ := 1024353644740818

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0082Witness : Array ℤ :=
  #[57, -48, -202, -52, -66, -207, 120, 166, 153, 48, 13, 92, -17, -73, -41,
  -220, 105, 155, 37, 22, 102, -105, -106, -132, 219, -165, 28, -181, 170,
  -108, -51, -146, -117, -18, -180, 29, 24, -45, 159, 15, 93, -4, 99, 115,
  -248, 58, -48, -148, 149, -98, 69, 43, -102, -60, 32, 0, 115, -54, 56, 22,
  29, -54, 48, 15, 73, 237, 242, -90, -111, 140, 141, 202, -60, -125, 87,
  90, -40, -228, -39, 42, 284, 168, -214, 130, -41, -182, 197, -27, -35, 51,
  -2, -90, -81, 150, 69, 16, 272, -38, -74, 46, 301, 118, -81, 207, 288,
  -34, -49, 67, 20, 210, -117, -118, 79, 158, 20, -161, 177, 143, -15, 77,
  158, 68, -119, -33, 42, 124, -140, -18, -80, -238, 289, 74, -122, -79,
  -156, -32, -266, -38, 120, -24, -157, 91, -202, 11, 80, 79, 72, 122, -113,
  201, -25, -67, 118, 216, 20, 134, -6, -108, 223, -360, -148, 320, -67,
  -175, 69, 44, -195, 93]

theorem fractionalNearFrameSubtreeG2R0082_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0082Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0082Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0082Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0082_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0082LowerBoundTable : List ℤ :=
  [-2, 1, 107, 154, 366, -324, 82, 144, 75, 9, -274, 341, -322, 643, 395,
  -15, 68, 1614, -61, -93, 236, 85, 962, 7, 251]

def fractionalNearFrameSubtreeG2R0082LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0082Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0082LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
