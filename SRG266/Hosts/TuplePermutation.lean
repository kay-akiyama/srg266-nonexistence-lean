/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Tactic

/-! # Reindexing finite tuples along list permutations -/

namespace SRG266
namespace Lattice

private theorem list_count_ofFn' {n : ℕ} {α : Type*} [DecidableEq α]
    (u : Fin n → α) (z : α) :
    (List.ofFn u).count z = ∑ i, if u i = z then 1 else 0 := by
  have hlist : ∀ l : List α,
      l.count z = (l.map (fun w => if w = z then 1 else 0)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons w l ih =>
        rw [List.count_cons, List.map_cons, List.sum_cons, ih]
        by_cases hw : w = z
        · simp [hw]
          omega
        · simp [hw]
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Two finite tuples whose value lists are permutations differ only by a
permutation of their coordinates. -/
theorem exists_fin_perm_comp_ofFn_perm {n : ℕ} {α : Type*} [DecidableEq α]
    {f g : Fin n → α} (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g (σ i) = f i := by
  have hfiber : ∀ z : α,
      Fintype.card {i : Fin n // f i = z} =
        Fintype.card {i : Fin n // g i = z} := by
    intro z
    have hcount : (List.ofFn f).count z = (List.ofFn g).count z :=
      h.count_eq z
    rw [list_count_ofFn' f z, list_count_ofFn' g z] at hcount
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter,
      Finset.card_filter]
    exact hcount
  exact ⟨Equiv.ofFiberEquiv fun z => Fintype.equivOfCardEq (hfiber z),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

end Lattice
end SRG266
