import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0025`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0025Mask : ℕ := 753839375110673

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0025Witness : Array ℤ :=
  #[-578, -969, -753, -779, -904, -963, 929, 508, 687, 668, 473, 204, 654,
  386, 534, 135, 368, 170, -129, -157, -164, 69, 69, 645, 311, 161, 210,
  368, 0, -166, -219, -81, 2, -90, 12, 225, 94, 726, -473, -470, 368, 470,
  421, 419, -465, -479, 89, -9, 639, 24, 129, -75, 246, -31, -50, -10, -48,
  -146, 62, 644, 7, -137, 265, 235, 76, 198, 169, 170, -143, 205, -68, -96,
  21, 85, 36, -291, 302, -290, 327, -437, -132, 47, 486, 345, 178, -4, -364,
  -118, -368, 163, -137, 111, -190, 147, 344, -296, 23, -93, 157, 19, -308,
  -380, -99, -30, 235, -810, -26, -513, -218, -728, -809, -135, -114, 931,
  1062, 182, -125, 270, -93, -91, -173, 69, -225, -12, 124, 2, 107, 31, 211,
  -68, -172, -85, 221, 21, 0, 115, -117, 99, 184, 346, -1, -5, -13, -212,
  -362, -8, -151, 318, 165, 69, 77, 26, 181, 9, 205, -271, 12, -122, -91,
  -52, 75, -3, -311, -291, 484, -263, -116, -74]

theorem fractionalNearFrameSubtreeG2R0025_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0025Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0025Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0025Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0025_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0025LowerBoundTable : List ℤ :=
  [126, -219, 32, 342, 31, 362, 664, 34, 658, 703, 661, -486, 102, 486,
  1081, -337, -376, 1038, 723, -875, 100, 102, 1305, 1954, -656]

def fractionalNearFrameSubtreeG2R0025LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0025Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0025LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
