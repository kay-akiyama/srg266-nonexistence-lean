import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0160`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0160Mask : ℕ := 6850829532830384

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0160Witness : Array ℤ :=
  #[144, -564, -300, -246, 41, 251, 281, -639, -5, -486, 410, 582, 724, -45,
  541, 250, 1101, 198, 472, 86, -691, 1124, 212, -552, 417, -162, -222,
  -645, -208, 214, 163, 898, -217, 759, 861, 620, -421, -904, 528, 675,
  -676, -188, 159, -83, 509, 1003, 855, -226, 282, 499, 823, -109, -937,
  271, 325, 743, 479, 759, -498, 933, -720, 696, 313, 408, 165, -116, -427,
  1205, 656, -149, 79, -839, 521, -83, 123, -142, -43, -208, -189, 659,
  -108, 157, -639, -278, -346, 300, -319, 845, -158, -576, 381, -96, -56,
  -589, 781, 209, 62, 143, -655, 534, 199, 417, -1092, -235, 381, 808, -142,
  -45, 47, -245, -77, -62, 1286, -951, 753, -242, 138, 136, -663, -272,
  -444, 1191, -572, 781, 92, 125, 52, 134, -19, 207, -209, 214, -660, -1373,
  650, 173, 208, 1956, -559, 262, -48, 220, 659, -561, 0, -538, 621, -441,
  192, 900, -664, 663, 571, -316, -611, -266, -54, 434, -68, 420, 152, -884,
  1013, -941, 0, -391, 0, -218]

theorem fractionalNearFrameSubtreeG3R0160_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0160Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0160Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0160Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0160_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0160LowerBoundTable : List ℤ :=
  [337, 134, -53, 786, 754, 698, 2488, 2276, 1201, 2277, 102, 1831, -520,
  885, 952, -151, -670, -238, 1550, 5164, 100, 3244, 856, 1435, 1464]

def fractionalNearFrameSubtreeG3R0160LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0160Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0160LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
