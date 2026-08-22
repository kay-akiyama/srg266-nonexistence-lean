/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Discriminant
import SRG266.Lattice.Frame
import SRG266.Lattice.Overlattice

/-!
# The maximal overlattice of the local Gram lattice

This module instantiates the abstract theory of `SRG266/Lattice/Overlattice.lean`
at the local Gram lattice `Λ = gramLattice G x` of a hypothetical
`srg(266, 45, 0, 9)`.  The two inputs are the denominator bound
`225 • Λ^∨ ⊆ Λ` (`gram_dual_denominator`) and the positive-definiteness of the
rational Gram form (`ratGramForm_nondegenerate`, `ratGramForm_isSymm`).

The output is a maximal integral overlattice `Λ̃ ⊇ Λ` with

* `15 • Λ̃^∨ ⊆ Λ̃` — the denominator has become squarefree, because
  `225 ∣ 15²` and maximality halves square factors (Lemma E);
* `Λ̃^∨ = T₃ + T₅` where `T_p = {y ∈ Λ̃^∨ : p • y ∈ Λ̃}` — obtained from the
  Bézout identity `1 = 2·3 − 1·5` at the level of elements;
* `Λ̃^∨/Λ̃` finite of exponent dividing `15`, so it is an elementary abelian
  `3`-group times an elementary abelian `5`-group.

That is exactly the datum the discriminant-group rigidity argument consumes, and
the second half of this module runs that argument: `disc_dim_le_two` bounds each
discriminant group `D_p = T_p/Λ̃` by dimension `2` over `ZMod p`, and
`nonempty_glueBasis_three` / `nonempty_glueBasis_five` produce the orthogonal
glue bases of `SRG266/Lattice/Discriminant.lean`.  So the whole discriminant
datum of `Λ̃` is at most two units mod `3` together with at most two units
mod `5` — the `(1 + 2 + 4) * (1 + 4 + 16) = 147` possibilities that the
complement certificate table enumerates.
-/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A maximal integral overlattice `Λ̃` of the local Gram lattice `Λ`, packaged
with the two facts that survive maximality: it is still a lattice, and its dual
has squarefree denominator `15`. -/
structure MaximalGramOverlattice (x : V) where
  /-- The overlattice `Λ̃` itself. -/
  carrier : Submodule ℤ (ratGramSpace G x)
  /-- It contains the Gram lattice `Λ`. -/
  gramLattice_le : gramLattice G x ≤ carrier
  /-- It is a lattice: finitely generated and of full rank. -/
  isLattice : Lattice.IsLattice ℚ carrier
  /-- It is maximal among the integral `ℤ`-submodules of the Gram space. -/
  isMaximal : Lattice.IsMaximalIntegral (ratGramForm G x) carrier
  /-- Its dual has denominator `15` rather than `225`. -/
  denominator : ∀ y ∈ (ratGramForm G x).dualSubmodule carrier, (15 : ℤ) • y ∈ carrier

/-- **Lemma M for the Gram lattice.**  A maximal integral overlattice of `Λ`
exists, and Lemma E has already reduced its denominator from `225` to `15`. -/
theorem nonempty_maximalGramOverlattice (hG : IsHypothetical G) (x : V) :
    Nonempty (MaximalGramOverlattice G x) := by
  obtain ⟨Ñ, hle, hlat, hmax, hden⟩ :=
    Lattice.exists_maximal_integral_overlattice_denominator (ratGramForm G x)
      (ratGramForm_nondegenerate G hG x) (ratGramForm_isSymm G x)
      (gramLattice_isLattice G x) (gramLattice_isIntegral G x)
      (k := (225 : ℤ)) (m := (15 : ℤ)) (j := 2)
      (gram_dual_denominator G hG x) (by norm_num)
  exact ⟨⟨Ñ, hle, hlat, hmax, hden⟩⟩

namespace MaximalGramOverlattice

variable {G} {x : V} (Λ : MaximalGramOverlattice G x)

/-- The dual lattice `Λ̃^∨`. -/
abbrev dual : Submodule ℤ (ratGramSpace G x) :=
  (ratGramForm G x).dualSubmodule Λ.carrier

/-- `Λ̃` is integral, hence contained in its own dual. -/
theorem le_dual : Λ.carrier ≤ Λ.dual := Λ.isMaximal.integral

/-- **The `{3, 5}` splitting.**  Every dual vector is the sum of one killed by
`3` and one killed by `5` modulo `Λ̃`. -/
theorem dual_eq_torsion_sup :
    Λ.dual = Lattice.torsionPart (ratGramForm G x) Λ.carrier 3 ⊔
      Lattice.torsionPart (ratGramForm G x) Λ.carrier 5 := by
  refine Lattice.dual_eq_torsionPart_sup (by norm_num) ?_
  intro y hy
  simpa using Λ.denominator y hy

/-- The dual quotient `Λ̃^∨/Λ̃` is annihilated by `15`. -/
theorem dualQuotient_nsmul_eq_zero
    (q : Λ.dual ⧸ Λ.carrier.comap Λ.dual.subtype) : (15 : ℕ) • q = 0 :=
  Lattice.quotient_nsmul_eq_zero (fun y hy => by simpa using Λ.denominator y hy) q

/-- The dual quotient `Λ̃^∨/Λ̃` is finite. -/
theorem dualQuotient_finite (hG : IsHypothetical G) :
    Finite (Λ.dual ⧸ Λ.carrier.comap Λ.dual.subtype) :=
  Lattice.finite_quotient_of_nsmul_le
    (Lattice.dual_isLattice (ratGramForm G x) Λ.isLattice
      (ratGramForm_nondegenerate G hG x)).fg (n := 15)
    (fun y hy => by simpa using Λ.denominator y hy)

/-- **Lemma R for the Gram lattice.**  Every discriminant group of the maximal
overlattice has dimension at most two.  (Only `p ∈ {3, 5}` can be nontrivial, by
the denominator bound.) -/
theorem disc_dim_le_two (hG : IsHypothetical G) (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (Lattice.discGroup (ratGramForm G x) Λ.carrier p) ≤ 2 :=
  Lattice.disc_dim_le_two (ratGramForm_isSymm G x) (ratGramForm_nondegenerate G hG x)
    Λ.isLattice Λ.isMaximal

/-- **Corollary S for the Gram lattice at `p = 3`.**  At most two glue vectors,
orthogonal modulo `ℤ`, with unit diagonal over `3`. -/
theorem nonempty_glueBasis_three (hG : IsHypothetical G) :
    Nonempty (Lattice.GlueBasis (ratGramForm G x) Λ.carrier 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Lattice.exists_orthogonal_glue_basis (p := 3) (q := 5) (by norm_num)
    (ratGramForm_isSymm G x) (ratGramForm_nondegenerate G hG x) Λ.isLattice
    Λ.isMaximal (by norm_num) Λ.dual_eq_torsion_sup

/-- **Corollary S for the Gram lattice at `p = 5`.** -/
theorem nonempty_glueBasis_five (hG : IsHypothetical G) :
    Nonempty (Lattice.GlueBasis (ratGramForm G x) Λ.carrier 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine Lattice.exists_orthogonal_glue_basis (p := 5) (q := 3) (by norm_num)
    (ratGramForm_isSymm G x) (ratGramForm_nondegenerate G hG x) Λ.isLattice
    Λ.isMaximal (by norm_num) ?_
  rw [sup_comm]
  exact Λ.dual_eq_torsion_sup

/-- **The discriminant datum of the maximal Gram overlattice.**  `Λ̃^∨` is
generated over `Λ̃` by at most two glue vectors at `3` and at most two at `5`,
each with unit diagonal over its prime and integral cross pairings.  This is the
datum consumed by the glue construction. -/
theorem exists_glueBases (hG : IsHypothetical G) :
    ∃ (S : Lattice.GlueBasis (ratGramForm G x) Λ.carrier 3)
      (T : Lattice.GlueBasis (ratGramForm G x) Λ.carrier 5),
      Λ.dual = Λ.carrier ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec) := by
  obtain ⟨S⟩ := Λ.nonempty_glueBasis_three hG
  obtain ⟨T⟩ := Λ.nonempty_glueBasis_five hG
  exact ⟨S, T, Lattice.dual_eq_sup_span_glue S T Λ.dual_eq_torsion_sup⟩

end MaximalGramOverlattice

end SRG266
