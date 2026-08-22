/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7SixGenericComponents
import SRG266.Hosts.E7FourEightGeneric
import SRG266.Hosts.E7FourEightSpecial
import SRG266.Hosts.E7SixGenericSixSpecial
import SRG266.Hosts.E7TwoTen

/-!
# Elimination of the five canonical residual E7 shell types

The centroid certificates reduce their surviving orbit pairs to five
canonical residual types.  The individual host modules exclude a shell
packing for each representative.  This module assembles those results into
one theorem indexed by `E7ResidualType`.
-/

namespace SRG266

/-- None of the five canonical residual E7 shells supports the required
220-vector packing. -/
theorem no_e7ResidualCanonical_packing (t : E7ResidualType) :
    IsEmpty
      (E7ShellPacking (e7ResidualCanonical t).1
        (e7ResidualCanonical t).2) := by
  cases t with
  | twoTen =>
      simpa [e7ResidualCanonical, E7TwoTenData.d₂,
        E7TwoTenData.d₁₀] using E7TwoTen.no_packing
  | fourEightGeneric =>
      simpa [e7ResidualCanonical, E7FourEightGenericData.d₄,
        E7FourEightGenericData.d₈] using
        E7FourEightGeneric.no_packing
  | fourEightSpecial =>
      simpa [e7ResidualCanonical, E7FourEightSpecial.d₄,
        E7FourEightSpecialCrossData.d₄,
        E7FourEightSpecial.d₈] using E7FourEightSpecial.no_packing
  | sixGenericSixGeneric =>
      simpa [e7ResidualCanonical, e7SixGenericProfile] using
        no_e7SixGenericSixGeneric_packing
  | sixGenericSixSpecial =>
      simpa [e7ResidualCanonical, E7SixGenericSixSpecialData.d₆g,
        E7SixGenericSixSpecialData.d₆s] using
        E7SixGenericSixSpecial.no_packing

end SRG266
