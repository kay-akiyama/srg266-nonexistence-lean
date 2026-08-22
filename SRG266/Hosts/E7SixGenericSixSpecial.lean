/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7SixGenericSixSpecialQuadraticCasts

/-!
# Exclusion of the residual `6g × 6s` E7 shell

The critical label class has 20 shell vectors and total multiplicity 55.
The weighted inner-product-two profile gives `xᵀ C x = 30 * 55`.
The critical shell is two copies of the ten edges of `K₅`. Splitting into
symmetric and antisymmetric coordinates and applying Cauchy--Schwarz to the
edge coordinates and the five vertex-incidence sums gives

`20 xᵀ C x ≥ 12 (∑x)²`,

which contradicts `33000 < 36300`.
-/

open scoped BigOperators Matrix

namespace SRG266
namespace E7SixGenericSixSpecial

open E7SixGenericSixSpecialData

/-- The residual `6g × 6s` shell cannot contain the required packing. -/
theorem no_packing : IsEmpty (E7ShellPacking d₆g d₆s) := by
  refine ⟨fun packing => ?_⟩
  have hpsd := criticalCentered_nonnegative
    (fun i => (packing.multiplicity (criticalVertex i) : ℚ))
  rw [← criticalQuadratic_cast packing, ← criticalTotal_cast packing,
    criticalQuadratic_eq packing,
    criticalTotal_eq_fifty_five packing] at hpsd
  norm_num at hpsd

end E7SixGenericSixSpecial
end SRG266
