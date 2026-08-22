import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0648`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0648Mask : ℕ := 36115473654599953

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0648Witness : Array ℤ :=
  #[423, 384, 362, 178, 530, 1512, 166, 218, 763, 129, 43, 779, -1409, -420,
  -111, -869, -731, -909, 0, 371, 29, -300, 74, 191, -145, 481, -437, -185,
  210, -283, 1257, 1976, 554, 207, 648, 361, 596, -366, -849, 0, 1183, 404,
  521, -126, 574, -1017, -1308, 589, 169, 143, 482, 123, -837, -196, 154,
  474, 119, -70, -380, -40, 36, 279, 31, 611, 500, -84, 205, -201, -506,
  213, 11, 479, -652, 723, -110, 42, 353, 308, 0, -92, 312, -26, 217, 302,
  113, 682, 617, 439, 143, 224, -555, 872, -464, -100, -200, -269, 307, 483,
  154, 169, 514, 513, 503, 349, 371, 11, -352, -485, -488, -45, 103, 18,
  -267, 96, 376, -129, -100, -157, -269, -37, 533, 492, -358, -677, 35, 501,
  -218, 311, 519, 968, -88, -65, -702, -280, -346, -73, 484, 313, 605, 1080,
  203, 180, -143, -498, 353, 44, 753, 166, 1818, 429, 888, -886, 1149, 594,
  -449, 307, 77, -58, -444, 572, -1133, 753, 726, -617, 1351, -743, -841,
  -690]

theorem fractionalNearFrameSubtreeG2R0648_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0648Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0648Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0648Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0648_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0648LowerBoundTable : List ℤ :=
  [1249, 1311, 42, 2841, 2522, 2287, 32, 1023, 32, 465, -142, 2436, 1725,
  100, 100, 2161, 2243, 3935, 3712, 749, 586, 2459, 108, 3174, 2850]

def fractionalNearFrameSubtreeG2R0648LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0648Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0648LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
