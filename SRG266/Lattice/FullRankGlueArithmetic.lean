/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ThetaEutaxyBoundary

/-!
# Finite arithmetic for the three full-rank glue cases

After theta-eutaxy forces the root lattice to be `D12`, `E7 + E7`, or `A15`,
the remaining discriminant groups have orders four, four, and sixteen.  This
file proves the finite choice arithmetic with ordinary kernel reduction and
arithmetic tactics; it uses neither `native_decide` nor `bv_decide`.

These lemmas are the finite endpoints consumed by the transport from an
abstract full-rank root embedding to its discriminant quotient:

* `D12`: the vector glue is excluded by its norm-one representative, leaving
  the two spinor classes (interchanged by the diagram automorphism);
* `E7 + E7`: integrality leaves only the diagonal nonzero class;
* `A15`: an element of exact additive order four is `4` or `12` modulo `16`,
  and both generate the unique order-four subgroup.
-/

namespace SRG266
namespace Lattice

/-! ## `D12` -/

/-- The four classes of `D12* / D12`. -/
inductive D12DiscClass where
  | zero
  | vector
  | spinorPlus
  | spinorMinus
deriving DecidableEq, Repr

namespace D12DiscClass

/-- The minimum norm in a `D12` discriminant class. -/
def minimumNorm : D12DiscClass → ℕ
  | .zero => 0
  | .vector => 1
  | .spinorPlus => 3
  | .spinorMinus => 3

/-- A nontrivial index-two glue which introduces no norm-one vector must be a
spinor glue. -/
theorem eq_spinor_of_nonzero_of_minimum_ne_one (c : D12DiscClass)
    (hne : c ≠ .zero) (hmin : c.minimumNorm ≠ 1) :
    c = .spinorPlus ∨ c = .spinorMinus := by
  cases c <;> simp_all [minimumNorm]

end D12DiscClass

/-! ## `E7 + E7` -/

/-- A discriminant class of `E7 + E7`; each factor has discriminant group
`Z/2Z`. -/
structure E7E7DiscClass where
  left : Bool
  right : Bool
deriving DecidableEq, Repr

namespace E7E7DiscClass

/-- Twice the coset minimum.  A nonzero class in one `E7` factor has minimum
`3/2`, so the pair has twice-minimum `3(a+b)`. -/
def twiceMinimumNorm (c : E7E7DiscClass) : ℕ :=
  3 * (c.left.toNat + c.right.toNat)

/-- Integrality of the glue-vector norm. -/
def HasIntegralNorm (c : E7E7DiscClass) : Prop :=
  c.twiceMinimumNorm % 2 = 0

/-- The only nonzero integral class is the diagonal class `(1,1)`. -/
theorem eq_diagonal_of_ne_zero_of_integral (c : E7E7DiscClass)
    (hne : c ≠ ⟨false, false⟩) (hint : c.HasIntegralNorm) :
    c = ⟨true, true⟩ := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;> simp_all [HasIntegralNorm, twiceMinimumNorm]

end E7E7DiscClass

/-! ## `A15` -/

/-- The cyclic discriminant group `A15* / A15`, represented by residues
modulo sixteen. -/
abbrev A15DiscClass := Fin 16

namespace A15DiscClass

/-- A residue has exact additive order four in `Z/16Z`. -/
def HasAdditiveOrderFour (x : A15DiscClass) : Prop :=
  (4 * x.val) % 16 = 0 ∧ (2 * x.val) % 16 ≠ 0

/-- The generators of the unique order-four subgroup of `Z/16Z` are `4` and
`12`. -/
theorem val_eq_four_or_twelve_of_orderFour (x : A15DiscClass)
    (h : x.HasAdditiveOrderFour) : x.val = 4 ∨ x.val = 12 := by
  fin_cases x <;> norm_num [HasAdditiveOrderFour] at h <;> norm_num

/-- Multiplication by `12` and by `4` have the same four residues modulo
sixteen.  This is the concrete statement that the two possible generators
above generate the same subgroup. -/
theorem twelve_multiples_eq_four_multiples (k : Fin 4) :
    (k.val * 12) % 16 = ((3 * k.val) % 4 * 4) % 16 := by
  fin_cases k <;> norm_num

end A15DiscClass

end Lattice
end SRG266
