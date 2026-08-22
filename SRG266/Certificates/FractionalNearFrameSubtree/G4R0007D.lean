import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0007`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0007Mask : ℕ := 1101189391024466

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0007Witness : Array ℤ :=
  #[368, -1386, -1562, -3215, 1172, 482, -674, 338, 462, 859, -825, 2668,
  -121, -126, 1989, 2609, 390, -686, 1346, -1567, 26, 1200, 508, -1020, 592,
  -1869, -213, -465, 479, -501, -2015, -1656, -3323, 1260, -528, 407, 284,
  2825, 641, 409, -422, 0, 157, 2035, 2261, 1389, -1397, -972, 855, 1652,
  -1389, -436, -1169, 446, -958, 445, -435, -129, 226, 2100, 353, 86, 35,
  1087, 623, -776, 1096, 179, -491, 2584, 583, -416, 1469, -304, -1624,
  -831, 554, -1320, 2888, 1738, -1467, 3225, 612, 3214, 2535, -96, -11,
  -498, -1002, -135, -1942, -1778, 134, 1229, -1791, 315, -285, -554, -1741,
  25, 18, 85, 439, 1603, -1364, -108, 525, 500, -1090, -203, 1195, -1281,
  -858, -276, 1749, -860, 1674, -1405, 293, 1657, 1001, -920, -872, -3188,
  -54, -344, -921, -1321, 1098, 193, 241, 589, 569, -374, 1601, -96, 92,
  -1283, -1024, 989, -740, -2293, -1030, -2672, -449, -849, 1075, -1016,
  -2104, -237, 756, 1033, -335, -42, -390, -381, 177, 1496, 163, 673, -469,
  -2184, -554, -132, 976, 5, -1148, 2852]

theorem fractionalNearFrameSubtreeG4R0007_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0007Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0007Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0007Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0007_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0007LowerBoundTable : List ℤ :=
  [-2137, -3429, 1146, 2722, -1768, 32, 31, 249, 810, 1283, 99, -1931,
  -2262, 3167, 3991, 2124, 1806, 4637, 1125, 1193, -10318, 5342, 5091, 4088,
  -4526]

def fractionalNearFrameSubtreeG4R0007LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0007Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0007LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
