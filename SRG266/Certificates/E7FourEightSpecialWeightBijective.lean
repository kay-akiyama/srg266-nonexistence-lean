/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightSpecialCrossBase

namespace SRG266
namespace E7FourEightSpecialCrossData

set_option maxRecDepth 100000

theorem firstWeight_bijective : Function.Bijective firstWeight := by
  decide +kernel

noncomputable def firstWeightEquiv : Fin 16 ≃ FirstWeight :=
  Equiv.ofBijective firstWeight firstWeight_bijective

@[simp] theorem firstWeightEquiv_apply (i : Fin 16) :
    firstWeightEquiv i = firstWeight i := by
  rfl

end E7FourEightSpecialCrossData
end SRG266
