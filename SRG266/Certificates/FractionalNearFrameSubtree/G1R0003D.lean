import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0003`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0003Mask : ℕ := 242903571619977

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0003Witness : Array ℤ :=
  #[-255, -241, -4, 29, 0, -51, 24, -28, 241, 181, 145, -49, -143, -48, -58,
  23, -8, 48, 101, -253, -166, 0, -30, 232, 17, -120, 83, -26, -29, -35,
  103, 8, -27, 22, 120, 131, -28, 0, 7, -78, -138, -49, 21, -64, -111, 196,
  105, 66, -104, -42, 128, 48, -11, -39, 183, 220, 207, 72, -33, 37, -23,
  72, 98, 88, 97, 141, -77, 76, 54, 45, 64, 121, -100, -89, -69, -44, 45,
  144, 144, -102, 141, 34, 24, -128, -131, -23, -11, -42, 123, -26, -18, 71,
  10, 98, -37, -206, 0, -105, -128, -42, -123, -36, 7, 7, -116, 60, -28,
  -34, 44, 33, 137, 19, 11, -115, 32, -118, -47, 57, 7, -125, 97, 51, 86,
  14, -84, 154, 235, 49, 130, 19, -101, -27, -117, 125, -100, 87, 86, -127,
  38, -43, 104, -60, 91, 141, 5, 21, -228, -187, -41, 108, 137, 27, 94, -45,
  -125, 110, 70, 9, 120, 22, 129, 244, -102, 156, 197, -17, 8, 52]

theorem fractionalNearFrameSubtreeG1R0003_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0003Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0003Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0003Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0003_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0003LowerBoundTable : List ℤ :=
  [-47, 213, 356, -234, 47, 2, 168, 64, 168, 686, 597, 397, 293, 22, 879,
  320, 460, 146, 182, -120, -125, 11, 635, 209, -278]

def fractionalNearFrameSubtreeG1R0003LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0003Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0003LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
