/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7FourEightSpecialWeightBijective

namespace SRG266
namespace E7FourEightSpecialCrossData

theorem allowedAt_characteristic_iff
    (s : Finset FirstWeight) (j : Fin 16) :
    allowedAt (characteristic s) j ↔ firstWeight j ∈ crossAllowed s := by
  classical
  constructor
  · intro h
    simp only [crossAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha
    let i := firstWeightEquiv.symm a
    have hwi : firstWeight i = a := by
      change firstWeightEquiv i = a
      exact firstWeightEquiv.apply_symm_apply a
    have hi : characteristic s i = true := by
      simp [characteristic, hwi, ha]
    have hp := (compatible_iff_nonnegative i j).mp (h i hi)
    simpa [hwi] using hp
  · intro h i hi
    have hs : firstWeight i ∈ s := by
      simpa [characteristic] using hi
    exact (compatible_iff_nonnegative i j).mpr
      ((Finset.mem_filter.mp h).2 (firstWeight i) hs)

end E7FourEightSpecialCrossData
end SRG266
