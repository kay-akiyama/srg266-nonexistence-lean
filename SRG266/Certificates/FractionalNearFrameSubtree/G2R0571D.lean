import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0571`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0571Mask : ℕ := 6847291257983564

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0571Witness : Array ℤ :=
  #[-114, 439, -136, -423, -165, 0, 200, -171, 93, 388, 113, 547, 54, 451,
  93, 517, -36, 525, 86, 214, 610, 274, 279, 51, -42, 97, -219, -371, -669,
  -377, -204, -456, -735, -479, 356, 113, 603, 701, 614, -202, 266, -292,
  623, -88, 681, -7, -228, -163, 565, 840, -860, -923, -70, 0, -376, 989,
  -238, -46, 335, -31, 419, 741, -722, -511, -142, -157, -396, 818, 73, 308,
  280, -190, 190, 807, 178, 43, 264, 407, 313, 184, -43, -367, -91, -312,
  -221, 230, 108, -403, 138, -455, 28, 342, -62, 496, 95, 126, 278, -181,
  -559, 324, -217, 138, 278, -373, -417, -322, 243, 402, -392, -455, 643,
  192, 629, 354, 336, -372, 40, -148, -223, 167, 336, 256, 0, -386, 465,
  219, 593, -112, 227, -582, 0, 120, 190, -7, -65, -147, -262, 148, -371,
  236, -639, 586, 801, -387, -40, 219, -253, 274, -335, 390, -154, 103,
  -355, 213, -459, 84, -317, -539, 114, 189, 188, 361, -332, -180, -75, 40,
  -236, -375]

theorem fractionalNearFrameSubtreeG2R0571_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0571Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0571Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0571Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0571_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0571LowerBoundTable : List ℤ :=
  [-11, 160, -970, 4, 570, 382, 1480, -108, 2023, 1859, 852, 87, 1362, 196,
  -1099, -1753, 3738, 337, 1474, -8, 403, -100, 2369, 751, 156]

def fractionalNearFrameSubtreeG2R0571LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0571Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0571LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
