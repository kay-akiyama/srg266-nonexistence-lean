import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0144`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0144Mask : ℕ := 1039471862005976

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0144Witness : Array ℤ :=
  #[160, 23, 276, 323, -316, -26, 407, 402, 228, -181, -75, 103, -255, -42,
  -29, -176, 194, 44, 263, 252, 54, -39, -161, -408, 24, 82, 305, 440, 285,
  198, 420, -291, -72, -61, -204, -96, 215, 573, 415, 0, -99, -154, -2, 348,
  -274, -32, -481, -178, 155, 133, -88, 207, 369, 263, 178, 86, 319, 493,
  -131, -261, 278, 195, -36, 57, 112, 45, -175, -683, -137, -73, 129, 346,
  -78, 170, 376, 372, 650, -148, -504, -102, -108, 156, 101, -251, -27, 4,
  -55, -138, -8, -233, 282, 33, -83, 210, -135, -248, -262, 21, 168, 305,
  163, 523, 326, 78, 422, 206, 444, 209, -83, 55, -203, -87, 29, 210, -94,
  488, 413, 45, 164, -80, -138, 87, 16, -60, 139, 50, -274, 0, 49, -178,
  233, 59, 134, -3, -19, -67, 61, -105, -101, 167, 12, -280, -120, 45, -51,
  215, 183, 221, 24, 50, 93, 41, 156, 24, 48, 164, 366, -204, 169, -191,
  -114, 110, -143, -172, -196, -189, 108, -282]

theorem fractionalNearFrameSubtreeG1R0144_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0144Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0144Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0144Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0144_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0144LowerBoundTable : List ℤ :=
  [388, 3, 888, 670, 2, 1066, 2, 621, 376, 773, 156, 512, 842, 1294, 520,
  1391, 873, 1246, 570, 1415, 1608, 14, 188, 281, 480]

def fractionalNearFrameSubtreeG1R0144LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0144Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0144LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
