/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The level-one weight-fourteen cusp space vanishes

The degree-two harmonic theta series of an even unimodular lattice of rank
twenty four has weight fourteen.  Once its analytic construction and
transformation law have put it in the level-one cusp space, no further
modular-form calculation is needed: multiplication by the discriminant
identifies that cusp space with the space of level-one forms of weight two,
and Mathlib proves that the latter is zero.

This file records the small, completely algebraic modular-form endpoint.
-/

namespace SRG266.Lattice

open ModularGroup ModularForm
open scoped MatrixGroups

/-- Every level-one cusp form of weight fourteen is zero. -/
theorem levelOne_weight_fourteen_cusp_eq_zero
    (f : CuspForm 𝒮ℒ 14) : f = 0 := by
  have htwo : Module.rank ℂ (ModularForm 𝒮ℒ 2) = 0 :=
    ModularForm.levelOne_weight_two_rank_zero
  have hmap : CuspForm.discriminantEquiv f = 0 :=
    (rank_zero_iff_forall_zero.mp htwo) _
  exact CuspForm.discriminantEquiv.map_eq_zero_iff.mp hmap

end SRG266.Lattice
