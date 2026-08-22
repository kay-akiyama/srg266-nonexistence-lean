import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0287`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0287Mask : ℕ := 5385088432456330

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0287Witness : Array ℤ :=
  #[-23, 17, 9, 27, -6, 15, -12, -5, -24, 0, 2, -28, 5, 7, 0, 20, -36, -3,
  24, -40, 0, 31, 53, 11, -31, 54, 2, 17, -66, -1, 37, 17, 13, 5, 26, 51,
  53, -84, -54, -6, 42, 27, 21, 4, -27, 32, -14, 8, 121, -48, 1, 55, -36,
  -13, -18, 26, -63, -22, 32, -6, -61, 3, 53, -35, 64, -71, 71, 5, -60, -19,
  48, 103, 27, 23, -74, -2, -5, 17, 46, -23, 31, 85, 10, 26, 7, 47, 82, 79,
  21, -34, -2, -27, -10, 26, -10, 19, 6, 55, 19, 42, 22, -5, -6, 49, 49, 25,
  17, -55, -56, 34, 13, 39, 24, 37, 17, 18, -6, 77, -106, 26, 5, -40, -18,
  16, -25, 35, 29, 60, -75, -61, -9, 69, -19, 23, -22, -17, -40, 60, 34, 27,
  -90, -20, -66, -4, 14, 55, 29, 39, 8, -36, 7, 16, 68, 48, -15, -11, 33,
  44, 41, 68, 33, -24, -50, -33, 69, 13, 80, 38]

theorem fractionalNearFrameSubtreeG2R0287_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0287Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0287Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0287Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0287_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0287LowerBoundTable : List ℤ :=
  [60, 143, 175, 99, 89, 60, 93, 2, 17, 194, 11, -104, 83, 68, 317, 174,
  319, 128, 104, 50, 160, 232, 80, 91, 237]

def fractionalNearFrameSubtreeG2R0287LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0287Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0287LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
