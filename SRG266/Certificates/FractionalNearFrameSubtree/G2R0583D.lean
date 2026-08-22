import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0583`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0583Mask : ℕ := 6850688345416296

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0583Witness : Array ℤ :=
  #[-122, -166, 334, -91, -97, 224, 31, -218, -33, -179, 164, 335, 223, 146,
  73, 94, 212, 34, -64, 391, 48, -143, 26, 36, -16, 158, 126, -525, -131,
  -21, -21, 186, -137, 117, 0, -80, -209, 86, 141, 159, -68, 35, -83, -41,
  187, -202, 30, 214, -65, -60, -114, -173, 15, 149, 604, 459, 644, -429,
  110, -181, -304, -180, -268, -179, -170, -288, 15, 0, 179, 19, -31, 37,
  -56, 105, -102, -4, 199, 330, -150, -108, -89, -55, 156, 71, 153, 235, -6,
  -61, 42, -64, 226, 69, -83, -323, 100, -241, -169, -101, -119, -56, -69,
  -12, 7, -280, -16, 174, 407, -31, 65, -338, -187, -228, -34, -111, 139,
  102, 162, 89, 127, 103, -109, -116, -75, -120, -159, 340, 430, 292, -49,
  635, -43, -41, 12, 249, 469, 112, 70, -14, 385, 322, -52, 47, -12, -2,
  172, 195, 83, 121, 173, 14, 142, -35, -201, 253, -33, 42, -59, -432, 15,
  -165, -69, -228, -261, 27, -231, -166, 346, 209]

theorem fractionalNearFrameSubtreeG2R0583_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0583Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0583Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0583Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0583_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0583LowerBoundTable : List ℤ :=
  [49, 348, 1, 382, 120, 0, 352, 358, 112, 666, 1157, 1181, 888, -97, -78,
  -176, 33, 391, 74, -489, 61, 1145, 81, -336, 762]

def fractionalNearFrameSubtreeG2R0583LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0583Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0583LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
