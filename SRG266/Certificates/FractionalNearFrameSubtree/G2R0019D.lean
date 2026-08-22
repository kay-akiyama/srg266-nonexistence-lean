import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0019`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0019Mask : ℕ := 684570142564625

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0019Witness : Array ℤ :=
  #[167, 54, -135, 0, -199, -57, 7, -26, -143, -211, -85, -74, 291, 356,
  189, 214, -89, 194, 80, 98, -138, 140, -113, 152, 285, 142, 9, 26, -86,
  -325, -75, -346, 0, -110, -41, -34, 97, 149, 174, 163, -23, 72, -209, 197,
  -68, 243, -146, -30, 57, -3, 362, -153, 44, -120, -49, -6, -58, -123,
  -170, -66, -24, -76, 117, 153, -131, -124, 106, -101, 109, 134, -136, 265,
  54, -32, 147, 30, 141, 180, 313, -284, 137, -35, 8, -50, -69, 0, 16, -168,
  -328, 2, 195, -20, -80, -150, 155, 18, 81, 155, 172, -226, -6, -83, 125,
  143, 277, 305, 337, -50, -357, -116, -170, -39, -122, -209, -133, -306,
  -247, 279, 536, 157, 116, -48, -125, 209, -33, 67, -44, -137, -67, -121,
  438, 35, 90, -37, 121, 311, -318, 152, -21, -90, 44, -74, -84, -148, 71,
  -11, 354, -49, -13, -142, 2, 26, -130, -27, -139, -318, -141, 271, -19,
  -147, -117, 332, -130, -113, -211, 90, 65, -105]

theorem fractionalNearFrameSubtreeG2R0019_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0019Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0019Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0019Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0019_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0019LowerBoundTable : List ℤ :=
  [-192, -251, -1, -285, 384, 250, 137, 374, -144, 373, 11, 98, -145, 1285,
  -57, 452, -492, 537, -317, 11, -86, 11, 10, 611, 287]

def fractionalNearFrameSubtreeG2R0019LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0019Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0019LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
