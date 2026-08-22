import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0026Mask : ℕ := 760430002426385

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0026Witness : Array ℤ :=
  #[-558, -250, -915, -709, -563, 0, 158, 305, -140, -248, 0, 290, 412, 665,
  148, 919, -496, 252, 212, 197, -544, -183, 372, 268, 493, 237, 147, 19,
  -398, -1, -291, -66, 122, 255, -213, -93, 54, 247, 494, 280, -71, -23,
  -259, -982, 321, 472, 184, -285, 606, 154, 209, 474, -241, -205, 270, 215,
  -124, -79, 138, 854, 102, 31, -34, 130, -44, -166, -273, 358, -108, 135,
  273, 310, 117, 303, 178, -418, 673, 481, 286, 238, -29, 4, -300, 59, -322,
  175, -46, -63, 490, 206, 1, -242, 194, -6, 178, -443, -97, -308, -53, 49,
  127, -328, -449, 158, -337, -1405, -1395, -552, -170, -832, 423, -1466,
  174, 1164, 1626, 74, 163, 68, -282, 60, 544, -166, 42, -346, 97, 402, -77,
  -177, 611, -190, 144, 6, 602, 325, -550, -872, 342, 342, -48, 29, 717,
  234, 462, 358, -258, 563, 91, -50, 343, -405, 503, -88, 24, -789, -306,
  744, 297, 394, -357, 416, 45, 372, 0, -294, -78, -24, 325, 261]

theorem fractionalNearFrameSubtreeG2R0026_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0026Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0026Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0026Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0026_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0026LowerBoundTable : List ℤ :=
  [-125, 844, 157, 31, -91, 1317, 865, 32, 689, 1263, 742, 1467, 100, 1016,
  366, -244, 603, 827, 956, 85, 1470, -188, -300, 1988, -1041]

def fractionalNearFrameSubtreeG2R0026LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0026Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0026LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
