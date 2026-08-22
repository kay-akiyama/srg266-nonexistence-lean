import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0064`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0064Mask : ℕ := 4980154404102289

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0064Witness : Array ℤ :=
  #[51, 406, 585, 1432, 609, -34, 1565, 726, 680, 1088, -160, -1184, -806,
  -690, -721, -994, -182, -748, -318, -453, -445, 56, -319, 490, 648, 280,
  965, 423, 1267, 73, 100, 1267, 416, 337, 360, 153, 0, -566, 97, -1031,
  233, -1334, 117, 1486, -264, -160, 74, -107, 225, 446, 463, 850, 148,
  -156, 64, -253, -104, 503, 334, 230, -124, -910, -209, -624, 0, 326, -359,
  332, -69, -164, 74, 588, -714, 91, 701, 291, -174, 535, 495, -101, 630,
  -737, 467, -243, 558, -10, -156, 108, -105, 389, 227, 932, -883, 60, 0,
  -982, 408, -219, 538, -220, 538, -32, 696, 636, -593, -514, 194, 323,
  -539, 412, 495, -100, -343, -370, 19, 872, -349, 132, -378, -286, 101,
  -303, 494, 881, -788, -883, 615, 20, 256, 633, 274, -206, -501, -1084,
  -1144, 395, -406, 1083, -293, 383, 337, -266, -313, 846, -1529, 569, 526,
  -662, 280, -357, -1008, 0, -271, 379, 671, 497, -570, -241, -155, 254,
  -220, 1228, -214, 1028, 655, -380, -393, 1040]

theorem fractionalNearFrameSubtreeG5R0064_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0064Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0064Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0064Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0064_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0064LowerBoundTable : List ℤ :=
  [-26, 643, 964, 419, -977, -236, 1262, 1485, 1009, 2013, 453, 99, 2669,
  1428, 99, 5936, -301, -771, 1138, 2418, 2652, 3218, -605, 99, 1489]

def fractionalNearFrameSubtreeG5R0064LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0064Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0064LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
