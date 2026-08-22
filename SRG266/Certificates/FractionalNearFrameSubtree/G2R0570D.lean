import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0570`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0570Mask : ℕ := 6846500676802066

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0570Witness : Array ℤ :=
  #[139, 13, -6, 35, 80, 94, 93, 176, -143, -28, 169, -246, -72, -52, -108,
  -124, -173, -154, -172, 19, -43, -25, 112, -9, -237, -439, 265, 340, 194,
  384, 155, 145, 170, 4, -113, 185, 69, -246, 270, -39, 38, -51, -175, 12,
  -2, -108, -293, 43, 30, 224, 45, 304, 148, 114, 0, -98, 163, -238, 269,
  -32, 118, 49, 259, -11, 183, -257, 417, -119, -46, 115, 89, 157, 48, -24,
  -163, 460, 99, -7, -86, 195, 83, 140, -71, 176, -62, -125, -19, 77, -96,
  -107, 62, -65, 20, -160, 146, -82, 169, 5, -18, 81, -7, -82, 21, 49, -105,
  81, 33, -208, -495, -178, 343, 527, 116, -13, 190, 175, 138, -23, 318,
  -283, 42, -196, 146, -225, -23, 105, 230, -13, 114, 26, -30, 54, 3, 88,
  -130, 13, 171, -66, 226, 144, 121, 99, 31, 165, 64, -179, 227, 16, -63, 1,
  0, -43, 226, -88, -55, 65, -52, -114, -80, 264, 112, -53, -39, 50, -153,
  -6, 48, -67]

theorem fractionalNearFrameSubtreeG2R0570_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0570Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0570Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0570Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0570_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0570LowerBoundTable : List ℤ :=
  [267, 472, 121, 38, 488, 407, 2, 318, 531, 571, -243, 713, 154, -30, 379,
  797, 292, 73, 274, 241, 556, 15, 1207, 296, 413]

def fractionalNearFrameSubtreeG2R0570LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0570Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0570LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
