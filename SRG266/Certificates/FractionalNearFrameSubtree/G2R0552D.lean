import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0552`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0552Mask : ℕ := 6839910049486354

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0552Witness : Array ℤ :=
  #[475, 347, 88, 155, 570, -280, -114, 274, 94, 11, 244, 85, -14, 216, 36,
  -717, -328, 468, -37, 335, -349, 85, 376, 563, -496, -386, 265, 151, -156,
  126, 512, 251, 406, 179, -210, 351, -19, -417, -333, -268, -648, 278, 382,
  325, 148, -146, 274, 686, -396, -39, -332, 132, 383, 211, -298, 36, 65,
  15, -145, -307, 365, 184, 213, 807, -319, 73, 342, -154, -416, -23, 185,
  89, 173, 641, -32, 362, -397, 407, -184, 161, -173, -102, 93, 196, 10,
  122, 96, -69, -228, -195, -628, 123, -123, 58, 111, -513, 47, 366, 601,
  693, 304, 105, 156, 20, 2, -149, 293, 0, 130, -505, -139, 0, 0, -308, 363,
  -80, 486, 225, -361, -301, -498, 196, 969, -46, 103, 284, 532, -263, -61,
  322, 958, 261, 378, 741, -249, 320, -104, -93, -449, -306, 376, 322, 492,
  380, 748, -14, -193, -191, -230, 132, -706, -404, -647, 453, -59, -357, 9,
  61, -62, 868, -645, 81, 558, 241, 653, 289, -14, 347]

theorem fractionalNearFrameSubtreeG2R0552_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0552Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0552Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0552Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0552_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0552LowerBoundTable : List ℤ :=
  [397, 640, 1516, -48, 130, 1189, 771, 703, 834, 1401, 1342, 2656, 10,
  1067, 735, 1807, 1525, -470, 1176, 1857, 491, 103, 1014, 360, 2287]

def fractionalNearFrameSubtreeG2R0552LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0552Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0552LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
