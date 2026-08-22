import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0600`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0600Mask : ℕ := 6874785452364400

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0600Witness : Array ℤ :=
  #[40, -50, -12, -67, 87, -17, -33, -34, -84, 97, 206, -1, 105, 128, 97,
  97, -37, 74, 1, 68, 58, 69, 28, 42, -41, -45, -11, -75, 101, 9, 95, 170,
  13, -23, -30, -28, -69, 22, -78, -51, -105, -60, 38, 119, 142, 115, -93,
  62, -71, -80, -40, -97, -105, -40, -105, -99, -32, 81, 21, -26, -19, 35,
  73, 94, -15, 28, 81, 8, 6, -14, -131, 14, 50, -3, -19, 82, 22, 85, 32, 42,
  -43, 37, -20, 0, 126, -82, -99, 85, 16, 80, 1, 42, -40, -85, -90, -65,
  129, 167, 65, 61, -97, 44, 14, 46, -42, -11, 92, -93, -67, -53, 62, 170,
  -38, -10, 0, 34, -41, -10, 91, 98, -19, 88, -42, 68, 13, -4, 78, 90, -7,
  21, 34, -35, 33, -23, 83, 40, -16, 47, 73, 133, -10, -13, 41, -99, 97, 13,
  56, 84, 25, 55, -69, 97, 54, -134, -49, -91, 12, -127, -23, -89, 9, -22,
  98, -65, 77, -128, -82, -70]

theorem fractionalNearFrameSubtreeG2R0600_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0600Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0600Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0600Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0600_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0600LowerBoundTable : List ℤ :=
  [49, 166, -48, 2, 185, 185, 2, 171, 152, 194, -136, 232, 38, 262, 82, 423,
  -7, 225, 457, 349, 24, 11, 287, 4, 204]

def fractionalNearFrameSubtreeG2R0600LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0600Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0600LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
