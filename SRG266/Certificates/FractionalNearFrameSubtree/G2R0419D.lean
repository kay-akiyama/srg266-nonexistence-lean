import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0419`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0419Mask : ℕ := 5776675876476422

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0419Witness : Array ℤ :=
  #[-377, -118, -721, 139, 178, 448, 491, 956, 151, 812, 1784, -1191, -548,
  -814, -456, -862, -122, 45, 365, 0, 375, -464, -322, -238, 162, -24, 103,
  -240, -29, 45, -21, 794, 356, -218, 21, 3, 310, -114, -530, -484, -18,
  128, 175, 525, 391, 14, 376, 90, -457, -752, -80, 98, 125, -202, 81, 27,
  188, 619, -982, 508, -94, -408, 713, 94, -1304, 388, -1274, -236, -105,
  178, 633, 142, 284, 48, -141, 224, 217, 24, 156, 106, 381, -73, -600, 34,
  -561, -95, 189, -519, -227, 399, 56, -220, -96, -39, -184, -367, -2, 374,
  -200, -402, -116, -431, 70, 373, -46, -407, 0, -88, 1212, 447, 677, 423,
  637, -185, -102, -18, -242, 237, -70, 453, 662, 305, 452, -574, -503, 344,
  259, 336, 728, 431, -252, -249, -102, 539, 240, 417, -188, 184, -197, 424,
  -406, 469, 810, 38, 304, 492, 185, -405, 474, -269, 211, 339, -118, -516,
  597, 13, 187, -183, -88, -342, 190, -54, -99, -998, 119, 234, -657, -659]

theorem fractionalNearFrameSubtreeG2R0419_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0419Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0419Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0419Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0419_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0419LowerBoundTable : List ℤ :=
  [-425, 563, -1334, 506, 653, 33, -546, -303, 181, 2121, 685, 1802, 3039,
  94, 572, -241, -90, 1675, 3404, 2361, 982, 100, 100, -923, 714]

def fractionalNearFrameSubtreeG2R0419LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0419Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0419LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
