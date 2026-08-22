import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0560`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0560Mask : ℕ := 6841900842329176

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0560Witness : Array ℤ :=
  #[3507, 3479, 12064, 4059, -141, -2417, -1202, 72, -5938, -7975, -1537,
  -3744, 4658, 7921, -1672, 3445, 7634, 712, 356, 7343, 9403, 2026, 1852,
  2264, -1173, -18228, -964, 4607, -1307, -9250, -9970, -211, 0, -3297,
  4333, 10249, 8076, -6064, -1251, 16217, 2481, 4164, 3933, -515, -2182,
  3012, -1900, -1400, -5466, 513, -4013, -5676, 12641, -2357, 2823, -9554,
  0, 12801, -5019, -1543, -2341, -4271, 11650, -5925, 6744, 0, -1591, 8898,
  -3126, 6783, -664, -1159, -4685, 6503, -3022, -4109, 3829, 3577, 5764,
  2075, 10023, -1046, -10117, 4195, 4661, -2010, 7439, 1610, 4721, 11379,
  -1112, 6338, 1239, -1497, -9413, 778, 2247, 4293, 3702, -560, -5605,
  -4075, 4029, -4360, 7255, 1194, 1665, 620, 4034, -4514, 8251, 12328,
  -4801, -18714, 532, 256, -4448, -3429, -2838, 1649, 5365, 10881, 4136,
  -2729, -3967, 2410, -4011, 9731, 1243, -6336, -9352, -2060, 2207, 3229,
  114, 12486, 19526, -3451, 3189, 1779, 4037, -925, -1361, 4303, -1249,
  10307, -117, 4291, 4162, -11904, 7821, -8582, -3380, 15052, 13363, -2139,
  19651, -484, 5722, 7888, 18345, -604, -3779, -11974, 1924, 2362, -1701,
  9037]

theorem fractionalNearFrameSubtreeG2R0560_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0560Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0560Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0560Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0560_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0560LowerBoundTable : List ℤ :=
  [11076, 22841, 20206, 15169, 6808, 20176, 9924, 5570, 20693, 36275, 17625,
  13407, 21394, 7070, -6981, -9570, 29343, 38702, -2960, 18193, 31661,
  32208, 1011, 7666, 18013]

def fractionalNearFrameSubtreeG2R0560LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0560Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0560LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
