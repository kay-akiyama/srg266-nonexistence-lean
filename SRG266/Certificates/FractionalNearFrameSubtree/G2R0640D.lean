import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0640`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0640Mask : ℕ := 11350098156426786

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0640Witness : Array ℤ :=
  #[-6360, -2110, 17945, 38630, 11602, 13592, -10440, 14753, 16908, 3960,
  5265, -12906, 22917, 15761, 15751, 0, 2732, 5377, 10836, 23046, -7302,
  4004, 44035, 3993, 33952, 850, 19897, 34321, 8058, -8049, -10957, 25874,
  15070, 17163, -6948, -15379, -14678, -12220, 5619, 7479, -68600, 10500,
  -25265, -7192, 24085, -10919, 32004, 42861, 19919, 7212, 28807, 5944,
  16152, 15668, -19118, -39608, -34935, 0, 15376, 14483, 49724, -15342,
  29918, -5318, 15516, -16900, 54731, -5202, -14093, 42102, 20237, 7462,
  24492, -33555, 0, 26225, 20936, 35768, -36839, 39314, 32308, 13734, -8641,
  36508, 19463, 31381, 26340, 41844, -1004, 37843, 48262, 3297, 19051,
  -40981, 5290, 6205, -1330, -10497, 24464, -15334, 3531, -14318, -2346,
  -11735, -7800, -16064, 0, -5784, 6548, 5139, 39338, 108419, 45290, 23772,
  8164, 3937, -3980, 23398, -26607, 4257, 18308, 3137, 23288, 9260, 33184,
  37929, 18691, 9620, -6712, 22211, 13398, -4697, 16133, 76636, -8022,
  -12731, 6874, -37700, 48087, 1554, 58401, -19951, -1612, 44786, 26694,
  -3247, 19655, 5833, 1228, 10640, 74264, -3364, -22845, 10802, 51764,
  -30830, 48314, -14054, 6032, -19647, -32043, 7922, 13744, 72727, -4018,
  50187, -23934, -14468]

theorem fractionalNearFrameSubtreeG2R0640_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0640Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0640Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0640Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0640_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0640LowerBoundTable : List ℤ :=
  [93970, 181101, 41586, 122959, 153325, 58416, 137501, 182289, 65199,
  188421, 22202, 203389, 100304, 71402, 177437, 79553, 80303, 124106, 48191,
  15474, 190444, 138079, 101337, 62532, 182142]

def fractionalNearFrameSubtreeG2R0640LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0640Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0640LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
