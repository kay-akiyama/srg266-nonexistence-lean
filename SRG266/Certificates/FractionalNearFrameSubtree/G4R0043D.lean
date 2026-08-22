import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0043`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0043Mask : ℕ := 5714009837256963

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0043Witness : Array ℤ :=
  #[1657, -411, 336, 855, -46, 732, 598, 747, -174, -2081, 1188, -649, 0,
  230, -614, -1052, -237, -588, 167, -200, -796, 246, -147, -666, -690,
  -3684, 0, 1624, 1281, 1722, 914, 3069, -292, 149, 557, -363, 950, 1685,
  -101, -536, 77, -85, -207, -147, 59, -781, 319, -272, 677, -634, 450,
  2005, 209, 86, 158, -196, -556, -1493, 484, 404, 925, 1228, 143, 1648,
  785, -391, 1030, 740, -802, 58, 304, -135, -798, 847, -32, 778, 673, -390,
  1903, -291, -418, 298, -122, -1594, 222, 344, -236, 702, 1419, 350, -549,
  69, -224, 422, 1297, 222, 1644, 1098, 389, -912, 45, -1449, 522, 607, 94,
  490, 1564, -1259, -1566, -505, -500, 316, -168, -94, -892, -419, -680,
  333, 1303, 611, -1152, -2955, -28, -376, -782, 282, 1558, 1622, -3208,
  596, -587, -50, -624, 1628, 156, -2333, 204, 732, 578, 125, 1053, 1348,
  1792, 1573, 205, 762, 185, 1050, -328, -102, -1784, -353, 503, 2010, -471,
  199, 66, 1199, -929, 346, -427, 3, 1252, -1204, 796, 54, -74, 417]

theorem fractionalNearFrameSubtreeG4R0043_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0043Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0043Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0043Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0043_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0043LowerBoundTable : List ℤ :=
  [532, 1098, 74, 32, 2228, 2243, 3350, 1855, 1332, 1411, 1512, 99, 1501,
  100, 844, 433, 100, 3481, 1618, 562, 3267, 710, 8121, 1887, 3062]

def fractionalNearFrameSubtreeG4R0043LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0043Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0043LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
