/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Branches.PureCore
import SRG266.Lattice.Hosts.E8Z7

/-!
# The two coreless branches

Three pure cases — `D₁₂⁺`, `A₁₅⁺` and `(E₇ ⊕ E₇)⁺` — need a coordinate
argument and have a module each.  The remaining two need one line of
arithmetic, and this file is
where they live:

| core `L₀` | host | why it is impossible |
| --- | --- | --- |
| `0` | `ℤ¹⁵` | a generator has norm three, and the zero lattice has only the norm zero |
| `E₈` | `E₈ ⊕ ℤ⁷` | `E₈` is even and three is odd |

Both arguments go through `SRG266.Lattice.PureCoreModel.generator_norm`, which
reads `⟨v_B, v_B⟩ = 3` inside the coordinate model, so neither branch needs the
centroid, the projector bound or a norm-three shell.  The only extra ingredient
is that there *is* a generator: the second subconstituent has `220` elements
(`SRG266.secondSubconstituent_card`), so it is nonempty.

The main results are `SRG266.Lattice.no_pure_z15Core` and
`SRG266.Lattice.no_pure_e8Core`, stated in the same shape as
`SRG266.Lattice.no_pure_d12PlusCore`: they consume the classification
hypothesis at the maximal orthonormal family produced by the norm-one splitting
of `SRG266/Lattice/Core.lean`.

The core of a purely embedded host has rank at least twelve and cannot be
covered by a lattice of rank `0` or `8`.
-/

namespace SRG266
namespace Lattice

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## There is a generator to argue about -/

/-- The second subconstituent of a hypothetical graph is nonempty: it has `220`
elements. -/
theorem nonempty_secondSubconstituent (hG : IsHypothetical G) (x : V) :
    Nonempty (SecondSubconstituent G x) :=
  Fintype.card_pos_iff.mp (by rw [secondSubconstituent_card G hG x]; omega)

/-! ## The zero core -/

/-- If the norm-one-free
core of the host is the zero lattice — that is, if the host is `ℤ¹⁵` — then a
pure embedding is impossible outright: a generator has norm three, but the
coordinate lattice of a `0 × 0` Gram matrix is trivial, so every value of its
form is zero. -/
theorem no_pure_z15Core {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {A : Matrix (Fin 0) (Fin 0) ℤ}
    (hclass : ∀ (k : ℕ) (u : Fin k → E.host.carrier),
      (∀ i, E.host.pairing (u i) (u i) = 1) →
      (∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) →
      (∀ w : E.host.carrier, (∀ i, E.host.pairing (u i) w = 0) → E.host.pairing w w ≠ 1) →
      IsHostCoreModel E.host u A) :
    False := by
  obtain ⟨k, u, hnorm, horth, hfree, -⟩ := E.host.exists_orthonormal_normOneFree
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hnorm
    (hclass k u hnorm horth hfree)
  obtain ⟨B⟩ := nonempty_secondSubconstituent G hG x
  have hgenNorm := M.generator_norm hG B
  have hgen : M.generator B = 0 := funext fun i => i.elim0
  rw [hgen] at hgenNorm
  simp [Matrix.toBilin'_apply] at hgenNorm

/-! ## The `E₈` core -/

/-- If the norm-one-free
core of the host is `E₈`, then a pure embedding is impossible outright: the core
is an even lattice (`SRG266.Lattice.e8_norm_even`) and the generators have odd
norm. -/
theorem no_pure_e8Core {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    (hclass : ∀ (k : ℕ) (u : Fin k → E.host.carrier),
      (∀ i, E.host.pairing (u i) (u i) = 1) →
      (∀ i j, i ≠ j → E.host.pairing (u i) (u j) = 0) →
      (∀ w : E.host.carrier, (∀ i, E.host.pairing (u i) w = 0) → E.host.pairing w w ≠ 1) →
      IsHostCoreModel E.host u e8Gram) :
    False := by
  obtain ⟨k, u, hnorm, horth, hfree, -⟩ := E.host.exists_orthonormal_normOneFree
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hnorm
    (hclass k u hnorm horth hfree)
  obtain ⟨B⟩ := nonempty_secondSubconstituent G hG x
  exact e8_norm_ne_three (M.generator B) (M.generator_norm hG B)

end Lattice
end SRG266
