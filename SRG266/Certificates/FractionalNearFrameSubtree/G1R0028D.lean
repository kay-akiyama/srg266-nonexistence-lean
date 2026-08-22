import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0028Mask : ℕ := 468286023782545

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0028Witness : Array ℤ :=
  #[-2373, -156, 16, -663, 0, -273, 929, 1035, 1254, 1197, -374, 788, -636,
  334, -747, -277, 236, 457, 1014, -1796, -265, 182, 566, 195, -1311, -159,
  -642, 0, -62, 986, 2046, 704, -496, 506, 710, -236, 120, -310, -570, -437,
  748, -361, -397, 486, 15, -993, 0, -1627, -1947, 678, 349, 1414, 1335,
  1271, 137, 405, 531, 361, 1580, 768, -67, 61, 533, 277, 119, 253, -123,
  -501, 7, -772, 541, -415, 370, 445, 849, 470, -104, -939, 414, 1019, 295,
  -460, 938, -58, 421, 1482, -752, 456, 582, 279, 706, 836, 333, 182, 1104,
  41, 87, -134, -519, -886, -266, 1920, 71, 1374, 1471, 1020, -582, 513,
  -231, 283, -4, -505, -1104, -429, -1070, 556, 34, -646, 419, 402, -1213,
  -525, -648, 1130, -401, 820, 444, -304, 113, -875, -115, 435, 337, -1187,
  -223, 26, -863, -256, -982, 741, 125, -361, -1115, 122, -350, -747, 1120,
  360, 676, 794, -409, -275, 121, -215, 1288, -529, 182, 1036, -499, -286,
  318, -563, 81, 103, 708, 363, -289, -800]

theorem fractionalNearFrameSubtreeG1R0028_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0028Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0028Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0028Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0028_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0028LowerBoundTable : List ℤ :=
  [236, -1295, 32, 1798, 2773, 1421, 32, 1471, 32, 3581, -1106, 396, 3891,
  -1949, -1612, 1630, 475, 5622, 99, 3049, 2152, 3519, 1744, 2383, 1938]

def fractionalNearFrameSubtreeG1R0028LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0028Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0028LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
