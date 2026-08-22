import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0544`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0544Mask : ℕ := 6833381699390994

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0544Witness : Array ℤ :=
  #[229, 252, -99, 232, 291, -393, -472, 50, -501, -734, 1231, 0, 651, -16,
  112, -391, 559, 491, 398, 969, -736, 990, 121, 73, -311, -484, -5, 606,
  -125, -735, 45, 535, 776, -887, 1602, -531, 480, -692, 426, 790, -580,
  855, -712, 10, -630, 1251, 338, -241, 387, -997, -17, -595, 729, 1078,
  -52, 495, -343, 31, 186, 213, 1053, -787, -466, -972, 88, 253, -1237, 419,
  391, 728, 298, 924, 983, 918, -1020, -561, -113, -115, 710, 885, 1096,
  -55, 273, -1120, -415, 655, -553, 200, 27, -145, -1280, -828, -153, 221,
  1337, -148, -144, 556, 642, 822, -424, 606, 519, 459, 443, 401, 626, -646,
  -1307, 519, 738, 342, 192, 436, -844, -155, -742, -267, 1338, -382, -355,
  222, -338, 188, 879, -549, 237, -104, -235, -756, 194, -897, -10, 125,
  416, 468, 586, -882, 668, -151, 127, 595, 459, 579, 706, 610, 396, -151,
  -286, 59, 387, -375, -572, -679, -76, 286, -625, -15, -837, -193, -221,
  -421, -7, 138, 342, 913, -721, -60]

theorem fractionalNearFrameSubtreeG2R0544_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0544Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0544Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0544Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0544_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0544LowerBoundTable : List ℤ :=
  [280, 561, -216, 557, 1793, 32, 1646, -24, 1067, 1934, -1841, 891, -2361,
  5664, -322, -670, -173, 1640, -107, 3059, 1332, 3940, 3511, 2744, 692]

def fractionalNearFrameSubtreeG2R0544LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0544Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0544LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
