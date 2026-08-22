import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0597`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0597Mask : ℕ := 6868257102269040

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0597Witness : Array ℤ :=
  #[305, 209, 727, -240, 375, -6, 650, 232, -204, -328, 231, -270, 60, 134,
  457, -276, 958, 11, -21, 756, 813, 639, 967, 136, -385, -718, -281, -329,
  -5, 323, 582, 578, -174, 732, -405, 8, -326, -147, 630, 556, -546, -769,
  -19, 60, -674, -79, -130, 456, 73, 392, 104, 214, -52, 66, 194, 167, 0,
  530, 648, 227, 1055, -303, -53, 665, -276, -163, 236, -842, 1532, -212,
  13, 470, -368, -127, 486, 568, -756, 1451, 799, 620, 372, 72, 370, 399,
  375, 161, 9, 705, 886, -588, 160, 302, 1008, -54, -796, -39, -888, -341,
  143, 205, 289, 275, 337, 241, -462, -171, -222, 28, -268, -217, 380, -849,
  -506, -494, 925, 506, 296, 83, 467, -330, -135, 422, -228, -534, 0, -257,
  104, -574, 448, 93, -241, 111, -106, -120, -289, -370, -82, -209, 118,
  290, 694, -5, -69, 15, 143, 463, 272, -79, 206, -10, 364, 137, 314, -13,
  193, -35, -203, 503, 39, 375, 50, 312, 552, 278, -19, -154, 61, -193]

theorem fractionalNearFrameSubtreeG2R0597_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0597Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0597Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0597Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0597_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0597LowerBoundTable : List ℤ :=
  [778, 739, 183, 779, 1441, 1078, 1757, 2737, 1508, -39, 9, 2349, -362,
  782, 1165, 1984, 875, 1029, 64, 2519, 1423, 1914, 3900, 1348, 2280]

def fractionalNearFrameSubtreeG2R0597LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0597Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0597LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
