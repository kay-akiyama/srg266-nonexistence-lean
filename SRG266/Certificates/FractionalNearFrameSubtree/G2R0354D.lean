import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0354`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0354Mask : ℕ := 5671096176548129

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0354Witness : Array ℤ :=
  #[78, -4, -1, 42, 52, -39, 42, 42, 0, 68, 45, 17, -81, -109, -38, 39, -47,
  -35, -77, 55, -192, -63, -89, 60, 10, 51, -50, -2, 59, -15, 39, 129, 197,
  41, 0, -93, 81, 85, 74, 7, -28, 12, -76, -118, -34, -74, 157, 62, 83, 54,
  -45, -7, -48, -161, 57, -19, 50, -73, 6, -53, -91, -76, -138, 34, 109, 81,
  98, 116, 78, -35, -5, 70, 74, -25, 54, 18, 62, 179, 30, -4, -25, 13, 5,
  61, -22, 10, -2, -37, -66, -35, 5, 50, -58, 63, 22, 61, -10, 67, -43, 8,
  -43, 28, 73, -91, 58, 9, 60, 27, -58, 5, -8, 169, -101, 18, -19, -114,
  -37, 157, -36, 104, -76, 93, 85, 20, -11, -28, -40, 29, 23, -13, 20, 36,
  -51, -18, 69, 83, -38, 75, -6, 17, 84, -33, -11, -34, -46, 25, 190, 106,
  27, -98, -49, -62, 8, -31, 97, 44, 119, -43, 27, -7, -1, 81, -152, -24,
  58, -26, 32, -62]

theorem fractionalNearFrameSubtreeG2R0354_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0354Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0354Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0354Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0354_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0354LowerBoundTable : List ℤ :=
  [36, 2, 48, -35, 126, 2, 1, 138, 331, 174, 495, 10, 381, 17, 28, -143,
  472, -50, 176, 93, 29, 243, 669, 113, 80]

def fractionalNearFrameSubtreeG2R0354LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0354Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0354LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
