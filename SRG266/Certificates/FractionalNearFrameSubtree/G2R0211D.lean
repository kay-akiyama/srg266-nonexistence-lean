import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0211`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0211Mask : ℕ := 2365490518278225

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0211Witness : Array ℤ :=
  #[-123, -26, -302, -373, -392, -318, -1401, -194, 710, 476, -1190, -69,
  221, 604, -107, 554, 571, 941, -476, 66, 466, -764, -64, 616, -485, 935,
  797, -221, 333, 145, -117, 1113, -382, 433, -16, 431, 456, -969, 790,
  -654, 435, -466, 236, -50, 0, -1, -620, -62, -254, 58, 951, 802, 23, 518,
  56, -954, -530, 366, -254, 990, 604, -128, -475, -534, -353, 446, -322,
  633, 282, 258, 167, -254, 357, 7, -425, 180, -194, 621, 761, -455, 921,
  311, 213, 260, -97, -153, -524, 275, -1232, -300, -496, 75, -73, -115,
  -682, 1389, 575, -268, -1, -607, 30, -433, -174, -677, -43, 697, -655,
  -730, 396, 591, -687, 61, -108, 180, -148, 1019, -1831, -1576, 1349, 551,
  780, 244, 852, 1413, 76, -867, 529, 439, 886, 18, 266, -139, -573, 904,
  -484, 842, -205, -89, 1226, -109, -210, -2, -178, 1366, 122, 971, 525,
  952, 1317, -290, -216, 0, 754, 706, 210, 72, -42, -970, 408, 359, 243,
  -747, -490, -604, -326, 53, -736, -568]

theorem fractionalNearFrameSubtreeG2R0211_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0211Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0211Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0211Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0211_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0211LowerBoundTable : List ℤ :=
  [106, 1761, -1367, 1238, 33, 33, 2158, 31, 31, 2256, 3636, 101, 2224,
  -1396, -1310, -946, 728, 2995, 2807, 1292, 1971, 2675, 906, 3388, 371]

def fractionalNearFrameSubtreeG2R0211LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0211Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0211LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
