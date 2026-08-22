import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0506`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0506Mask : ℕ := 5811644419418792

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0506Witness : Array ℤ :=
  #[-4858, -6084, -1705, -19188, -4377, 10799, 16638, 6863, 12424, 8593,
  -3015, -4342, -8913, 8005, 3916, 5125, 875, -23072, -5257, 1858, 7507,
  -4180, 4790, -9973, -3437, 17639, 8948, -1629, -10352, 4204, 540, 8125,
  1247, -15113, -28085, 14634, 14882, 11297, 6920, -20450, 5958, 6630,
  -1066, 6064, 4163, -5793, 9789, 10039, -2955, -14694, 0, 2399, 20923,
  5589, -10020, -16722, -25893, -8646, -9355, -1804, -1445, 10502, 9398,
  -18147, 464, -1002, -9499, 13013, -1237, 17370, 1191, 8749, -10912, 21896,
  11748, -12686, 13662, 1201, 11048, 6555, -5690, -27352, -6318, 4225,
  -5715, 13574, 0, 3329, -23353, -2315, 9747, -14158, 6641, 758, 7900,
  -3297, -8565, -12253, 4985, -13562, 4066, -11912, 10430, -677, 13895,
  -1077, 10315, 17106, 1008, 8607, 642, -5821, -245, -11685, -9889, -9689,
  -5527, 11646, 2919, 9991, -2926, -15006, -3731, -11828, -15015, -768,
  3651, -4431, -8099, -2790, 4850, 13305, 10604, 7071, -16524, 9055, 5224,
  -19795, 17240, -7317, -4283, 22084, -9593, -3520, -1071, -4864, -3034,
  4918, -18370, 3060, 1411, -5156, -1026, 4997, 10336, 202, -10533, -4730,
  23136, -1246, 2018, 9001, -14189, -19643, 14167, -7623, -2940, 9961]

theorem fractionalNearFrameSubtreeG2R0506_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0506Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0506Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0506Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0506_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0506LowerBoundTable : List ℤ :=
  [-26725, -4121, 24653, -19335, 32, 9124, -31494, -4107, 19385, 20490,
  -52626, 4688, 20298, -6357, 8430, 23693, 57785, -19529, 99, -55613, 18199,
  -23855, -8994, -4224, 19423]

def fractionalNearFrameSubtreeG2R0506LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0506Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0506LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
