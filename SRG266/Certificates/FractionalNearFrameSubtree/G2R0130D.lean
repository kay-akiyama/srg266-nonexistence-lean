import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0130`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0130Mask : ℕ := 1353133242098314

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0130Witness : Array ℤ :=
  #[26, 73, -5, 115, 31, 83, 0, -145, -41, -156, 64, -38, 164, 46, 7, 188,
  -13, 259, 44, 20, 158, 11, 161, 39, -61, 109, 88, 111, -111, 15, -131,
  -277, -143, 136, 83, -33, -73, 141, 53, 190, -92, 97, 115, 80, -28, 13,
  -22, 72, 240, -12, 61, -143, -157, -69, 43, 0, -254, 103, 8, 48, 272, 0,
  36, -108, 84, 77, 79, 236, 74, -22, 45, 85, 9, -107, 148, 91, 33, -27, 66,
  -136, -95, 87, 116, -109, -68, -60, -35, 102, 143, 64, 264, 303, 224, 257,
  16, 193, -63, -52, 69, 23, 317, -54, 43, -40, 54, 2, -15, -47, -128, -268,
  -108, 23, 100, -17, 148, -14, 196, 34, -1, -57, 98, -7, 32, -66, 39, -11,
  -190, -141, 133, 131, -44, 23, 130, -19, -19, 110, 104, 102, -89, 66, 82,
  77, 137, -54, 82, 51, 103, -155, -13, -7, -161, 5, 52, 14, -138, -136,
  -35, 59, -152, -3, -84, 102, 59, -30, -105, 0, -113, 5]

theorem fractionalNearFrameSubtreeG2R0130_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0130Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0130Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0130Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0130_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0130LowerBoundTable : List ℤ :=
  [169, 3, -19, 355, 371, 780, 3, 308, 362, -193, -403, 520, 66, 306, -434,
  350, 561, 410, 1004, 222, 337, 92, 571, 119, 1087]

def fractionalNearFrameSubtreeG2R0130LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0130Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0130LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
