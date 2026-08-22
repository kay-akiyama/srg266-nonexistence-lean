import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0479`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0479Mask : ℕ := 5810321601511826

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0479Witness : Array ℤ :=
  #[-119, -592, 511, -34, -467, -320, 223, 999, 461, 666, -429, 487, 191,
  65, 456, -486, 642, 335, -469, 230, -33, 615, 201, 182, 96, -13, -185, 50,
  -727, -233, 169, 378, 582, 401, -254, -425, -35, 474, 390, 162, 322, 10,
  -829, -579, -26, 984, -248, -124, -124, -82, 728, 869, 622, 1002, -359,
  81, 166, -679, 522, -469, -348, 764, 615, 200, 495, 41, 643, -64, 170,
  -237, -187, 232, 338, -263, 135, 45, -245, 42, 242, 449, 203, -44, 278,
  -177, 388, -188, 106, 715, -63, -367, 204, -74, 159, 577, 371, -224, -424,
  389, 147, 90, -7, 22, -123, 166, -534, -30, -301, -31, -429, 218, 116,
  -605, -168, -211, -408, 20, -63, 443, 671, -260, 93, -313, -521, 199, 93,
  46, 221, 487, 609, 226, 24, -508, -309, 337, -28, 86, 51, -413, 276, -103,
  -179, 323, -818, -306, -307, -107, 208, 211, 236, 568, -52, 516, -95, 78,
  -250, 129, 682, -243, 240, -202, -278, 515, -400, -332, 129, -375, 472,
  229]

theorem fractionalNearFrameSubtreeG2R0479_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0479Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0479Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0479Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0479_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0479LowerBoundTable : List ℤ :=
  [290, 32, 1143, 32, 1448, 458, 750, 533, 1431, 736, -590, 871, -236, 406,
  1765, 2632, 2317, 464, -44, 1167, 1451, 1779, 1949, 1525, 100]

def fractionalNearFrameSubtreeG2R0479LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0479Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0479LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
