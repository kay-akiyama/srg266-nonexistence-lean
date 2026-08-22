import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0156`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0156Mask : ℕ := 1378541314212194

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0156Witness : Array ℤ :=
  #[246, -30, 2, 6, -70, 42, 325, 294, 384, 391, 340, -204, -394, -410,
  -364, -365, -25, 255, -127, -54, -177, -35, -42, -123, -115, -166, 243,
  208, 250, 112, 22, 102, 93, 84, 58, -250, -294, 255, 239, -96, -275, -356,
  132, 223, 111, 299, 208, 245, 143, 164, -241, -196, -259, -79, -57, -76,
  -81, -216, -328, 69, 89, -11, 23, 64, -144, -20, 127, -22, 2, 116, -40,
  68, -176, -96, -35, 106, -63, 30, -14, 67, -119, -101, -169, 5, 164, 118,
  54, 176, -33, 38, -127, 140, 145, 94, 68, 61, -19, 19, -2, -69, 34, -94,
  15, -65, 94, 4, 42, -82, -120, 4, 63, -64, 14, -66, -38, -94, -111, -136,
  58, -28, 76, -36, -53, 6, 67, 107, 23, 123, 25, 18, -17, -18, 15, -27,
  112, 96, -52, -229, -34, -19, 155, 41, 52, 38, -21, -14, 30, -2, 9, -19,
  6, 98, 119, -23, -43, 8, 89, -76, 185, 105, -165, 66, 2, 30, 140, 26, 102,
  21]

theorem fractionalNearFrameSubtreeG2R0156_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0156Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0156Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0156Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0156_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0156LowerBoundTable : List ℤ :=
  [-101, 122, 158, 58, 1, 3, -67, -37, 232, 107, 47, 9, 10, 487, 260, 9,
  649, -73, 101, -138, 246, 171, 633, -185, 153]

def fractionalNearFrameSubtreeG2R0156LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0156Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0156LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
