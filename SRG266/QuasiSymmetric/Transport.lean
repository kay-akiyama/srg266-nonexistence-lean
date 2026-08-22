/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.DerivedResidual

/-!
# Transporting a residual structure along an isomorphism of derived designs

A concrete quasi-symmetric `2-(56, 12, 9)` design and a point determine a
`SRG266.QuasiSymmetric.Derived45` on an *anonymous* `55`-element type together
with its `SRG266.QuasiSymmetric.Residual165`. The residual structures of the
sixteen listed designs live on
`SRG266.QuasiSymmetric.Edge11`.  This file is the bridge: a relabelling of the
`55` points and the `45` blocks carries a residual structure across, so a
`Derived45` isomorphic to one that carries no residual structure carries none
either.

## Main results

* `SRG266.QuasiSymmetric.Derived45Iso`
* `SRG266.QuasiSymmetric.Residual165.transport`
* `SRG266.QuasiSymmetric.isEmpty_residual165_of_iso`
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-- An isomorphism of derived designs: a relabelling of the `55` points and a
permutation of the `45` blocks that match the block sets up. -/
structure Derived45Iso {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (E : Derived45 P) (F : Derived45 Q) where
  /-- The relabelling of the points. -/
  point : P ≃ Q
  /-- The relabelling of the block indices. -/
  index : Equiv.Perm (Fin 45)
  /-- The two relabellings match the blocks up. -/
  map_block : ∀ i, (E.block i).image point = F.block (index i)

namespace Derived45Iso

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {E : Derived45 P} {F : Derived45 Q}

/-- The blocks of the target, read through the isomorphism. -/
theorem block_eq_image (iso : Derived45Iso E F) (i : Fin 45) :
    F.block i = (E.block (iso.index.symm i)).image iso.point := by
  rw [iso.map_block, Equiv.apply_symm_apply]

end Derived45Iso

namespace Residual165

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {E : Derived45 P} {F : Derived45 Q}

/-- **Transport of a residual structure.**  Relabelling the points of a derived
design carries its residual structure to the target. -/
def transport (iso : Derived45Iso E F) (R : Residual165 E) : Residual165 F where
  res n := (R.res n).image iso.point
  res_card n := by
    rw [Finset.card_image_of_injective _ iso.point.injective, R.res_card]
  res_meet m n hmn := by
    rw [← Finset.image_inter _ _ iso.point.injective,
      Finset.card_image_of_injective _ iso.point.injective]
    exact R.res_meet m n hmn
  cross_meet i n := by
    rw [iso.block_eq_image i, ← Finset.image_inter _ _ iso.point.injective,
      Finset.card_image_of_injective _ iso.point.injective]
    exact R.cross_meet _ n
  res_rep q := by
    classical
    have hset : (Finset.univ.filter fun n => q ∈ (R.res n).image iso.point) =
        Finset.univ.filter fun n => iso.point.symm q ∈ R.res n := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        simpa using hp
      · intro h
        exact ⟨iso.point.symm q, h, by simp⟩
    rw [hset, R.res_rep]
  res_inj m n hmn := by
    refine R.res_inj ?_
    have h := congrArg (Finset.image iso.point.symm) hmn
    simpa [Finset.image_image] using h

end Residual165

/-- **Transport of the contradiction.**  A derived design isomorphic to one that
carries no residual structure carries none either. -/
theorem isEmpty_residual165_of_iso {P Q : Type*} [Fintype P] [DecidableEq P]
    [Fintype Q] [DecidableEq Q] {E : Derived45 P} {F : Derived45 Q}
    (iso : Derived45Iso E F) (h : IsEmpty (Residual165 F)) : IsEmpty (Residual165 E) :=
  ⟨fun R => h.elim (R.transport iso)⟩

end SRG266.QuasiSymmetric
