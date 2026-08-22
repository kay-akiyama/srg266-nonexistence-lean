import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0579`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0579Mask : ℕ := 6850658482883176

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0579Witness : Array ℤ :=
  #[650, -723, 730, 66, 409, -685, -101, -296, -305, 620, 703, 107, 556,
  -34, 488, -48, 241, 168, 567, 25, -132, -212, -147, 321, -756, 489, 370,
  -682, 538, 256, 712, 500, -169, -523, 449, -187, -153, -693, -525, -515,
  513, 194, -337, -494, -993, 947, 200, -14, 599, 507, 96, -76, 318, 405,
  1204, 218, -1306, 953, -251, 13, -1103, -82, 637, -622, -1180, 409, -332,
  373, -857, 278, -719, 10, 588, 54, -642, -107, -222, -286, -455, -480,
  -742, -721, -258, 171, -512, 475, 98, 127, -506, 530, -745, 531, 577, 369,
  -347, 486, -157, -484, -553, -615, -503, 503, 542, -322, -637, -684, 146,
  111, 339, 392, 1059, 685, -905, 0, -54, -217, 1490, -247, 67, 373, -512,
  514, -172, 477, 318, -56, 200, -217, 351, -118, 625, 105, 107, -323, 39,
  -160, 782, 656, 75, 775, -520, 477, 132, -1091, -625, -908, 580, -357,
  772, 136, -597, -430, -638, -174, 398, -3, 166, -954, -256, 334, -1026,
  420, -331, -186, 0, 666, 0, -616]

theorem fractionalNearFrameSubtreeG2R0579_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0579Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0579Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0579Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0579_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0579LowerBoundTable : List ℤ :=
  [-536, -110, -213, -1026, 33, 33, -661, 737, 31, 652, 1898, -605, -731,
  -529, 100, 99, 2342, -1785, 1000, 1501, -211, 1351, -1780, -241, 843]

def fractionalNearFrameSubtreeG2R0579LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0579Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0579LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
