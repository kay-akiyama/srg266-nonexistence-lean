import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0019Mask : ℕ := 1041396194510929

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0019Witness : Array ℤ :=
  #[581, -508, -574, 649, -832, -108, -588, 227, -874, -598, 555, 943, 479,
  55, 1007, 1054, 132, -143, 552, -557, -978, 130, 533, 843, -148, 196, 0,
  171, -815, -83, 878, -590, 1308, -598, -777, -381, 684, -6, 959, -708,
  -563, -1792, 354, 954, 825, 428, -708, -184, 107, -33, -755, 1084, 619,
  335, 97, 170, -204, -910, -1170, -690, 116, 224, 258, 953, -220, 353, 278,
  175, 150, 936, 398, 306, 237, -444, -343, -420, 277, -644, -892, -392,
  -942, 441, -225, -174, -220, -584, -187, -317, -178, -173, 912, 756, -171,
  599, 458, -654, 328, 602, 1406, 671, -539, -132, -432, 533, 147, -265,
  -72, 128, 183, 560, -84, 704, 390, 663, -339, 145, -145, 111, -36, 1452,
  537, -357, -750, -163, -583, 512, 583, 959, 864, 763, -1224, -764, -315,
  703, -1128, -98, 370, 168, 230, 0, -528, 519, -990, 862, 153, 224, 197,
  -916, 1156, -524, -393, -139, 12, -47, 246, -355, 15, -531, -29, 705,
  -1154, 573, -635, -265, -289, -533, 46, 134]

theorem fractionalNearFrameSubtreeG5R0019_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0019Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0019Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0019Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0019_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0019LowerBoundTable : List ℤ :=
  [-791, 90, -320, -132, 455, -409, 201, 637, 517, 964, 1631, -401, 286,
  1559, -1102, 101, 3019, 2288, 3294, 100, 3042, 100, -308, -4, 694]

def fractionalNearFrameSubtreeG5R0019LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0019Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0019LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
