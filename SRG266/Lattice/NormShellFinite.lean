/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.NormTwoRootFinite

/-!
# Finiteness of every integral norm shell

The theta-series layer needs finite sums over vectors of every fixed
nonnegative norm, not only over roots.  The coordinate proof used for the
norm-two shell works verbatim.  Unimodularity represents the coordinate
functionals by lattice vectors, and Cauchy--Schwarz puts every coordinate in
an explicit finite interval.
-/

namespace SRG266.Lattice

/-- The vectors of integral norm `q` in a positive-definite unimodular
lattice. -/
def NormShell {n : ℕ} (L : PDUnimodularLattice n) (q : ℕ) :=
  {v : L.carrier // L.pairing v v = (q : ℤ)}

/-- Every fixed nonnegative norm shell is finite. -/
theorem normShell_finite {n : ℕ} (L : PDUnimodularLattice n) (q : ℕ) :
    Finite (NormShell L q) := by
  letI := L.moduleFree
  letI := L.moduleFinite
  let b : Module.Basis (Fin n) ℤ L.carrier :=
    Module.finBasisOfFinrankEq ℤ L.carrier L.rank
  choose d hd using fun i : Fin n => L.unimodular.2 (b.coord i)
  let bound : Fin n → ℤ := fun i => (q : ℤ) * L.pairing (d i) (d i) + 1
  let BoxCoord : Fin n → Type := fun i =>
    {a : ℤ // a ∈ Set.Icc (-bound i) (bound i)}
  letI (i : Fin n) : Fintype (BoxCoord i) :=
    (Set.finite_Icc (-bound i) (bound i)).fintype
  let encode : NormShell L q → (∀ i, BoxCoord i) := fun r i =>
    ⟨b.equivFun r.1 i, by
      have hcoord : b.equivFun r.1 i = L.pairing (d i) r.1 := by
        change b.coord i r.1 = L.pairing (d i) r.1
        exact (DFunLike.congr_fun (hd i) r.1).symm
      have hcs := L.pairing.apply_sq_le_of_symm
        (pairing_self_nonneg L)
        (LinearMap.BilinForm.isSymm_iff.mp L.symmetric) (d i) r.1
      rw [r.2] at hcs
      have hdnonneg := pairing_self_nonneg L (d i)
      have hqnonneg : (0 : ℤ) ≤ q := by exact_mod_cast (Nat.zero_le q)
      change -bound i ≤ b.equivFun r.1 i ∧
        b.equivFun r.1 i ≤ bound i
      dsimp only [bound]
      rw [hcoord]
      constructor <;> nlinarith⟩
  exact Finite.of_injective encode fun r s hrs => by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    exact congrArg Subtype.val (congrFun hrs i)

/-- The canonical finite instance for a norm shell. -/
noncomputable instance normShellFinite {n : ℕ}
    (L : PDUnimodularLattice n) (q : ℕ) : Finite (NormShell L q) :=
  normShell_finite L q

/-- A noncomputable enumeration of a fixed norm shell. -/
noncomputable instance normShellFintype {n : ℕ}
    (L : PDUnimodularLattice n) (q : ℕ) : Fintype (NormShell L q) :=
  Fintype.ofFinite _

/-- The norm-two shell is definitionally the root type. -/
def normShellTwoEquivNormTwoRoot {n : ℕ} (L : PDUnimodularLattice n) :
    NormShell L 2 ≃ NormTwoRoot L :=
  Equiv.refl _

end SRG266.Lattice
