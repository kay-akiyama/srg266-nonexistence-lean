/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ConcreteCodeData

/-!
# The listed E7 pairs are expanded

Every listed canonical profile pair is exhibited as the canonical pair of two
profiles drawn from the fibres of one listed key pair.  Both checks are linear
in the 956 witnesses, so the reverse inclusion of the expansion costs no
search at all.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- The listed canonical pairs are the canonical pairs of the witnesses. -/
theorem e7ConcreteWitnesses_pairs :
    e7ListedCanonicalArrayPairs =
      e7ConcreteWitnesses.map
        (fun witness => e7CanonicalComponentArrayPair witness.2.1 witness.2.2) := by
  decide +kernel

/-- Every witness is drawn from the fibres of a listed key pair. -/
theorem e7ConcreteWitnesses_fibres :
    e7ConcreteWitnesses.all (fun witness =>
      decide (witness.1 ∈ e7ConcreteCodePairs) &&
        decide (witness.2.1 ∈ e7ConcreteFibreOf witness.1.1) &&
          decide (witness.2.2 ∈ e7ConcreteFibreOf witness.1.2)) = true := by
  decide +kernel

end SRG266
