/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Search.LRAT

/-!
# Boolean semantics for the LRAT formula language

Mathlib's LRAT checker states unsatisfiability using `Sat.Valuation`, whose
variables are propositions and whose clause semantics is written in
continuation form.  Executable certificate encoders are more naturally proved
correct against Boolean valuations.

This file supplies the exact bridge.  It contains no SAT search and no
reflection tactic: a Boolean formula evaluation equal to `true` constructs the
ordinary propositional satisfaction witness consumed by an LRAT refutation.
-/

namespace SRG266.Search

/-- Evaluate a SAT literal under a Boolean assignment. -/
def evalLiteral (assignment : ℕ → Bool) : Sat.Literal → Bool
  | .pos i => assignment i
  | .neg i => !assignment i

/-- Evaluate a clause as a disjunction of its literals. -/
def evalClause (assignment : ℕ → Bool) (clause : Sat.Clause) : Bool :=
  clause.any (evalLiteral assignment)

/-- Evaluate a formula as a conjunction of its clauses. -/
def evalFmla (assignment : ℕ → Bool) (fmla : Sat.Fmla) : Bool :=
  fmla.all (evalClause assignment)

/-- Regard a Boolean assignment as Mathlib's propositional SAT valuation. -/
def boolValuation (assignment : ℕ → Bool) : Sat.Valuation :=
  fun i => assignment i = true

/-- Boolean truth of a clause implies Mathlib's continuation-form clause
satisfaction. -/
theorem satisfies_of_evalClause_eq_true (assignment : ℕ → Bool) :
    ∀ clause, evalClause assignment clause = true →
      (boolValuation assignment).satisfies clause := by
  intro clause
  induction clause with
  | nil => simp [evalClause]
  | cons literal clause ih =>
      cases literal with
      | pos i =>
          intro hEval hfalse
          have hcases : assignment i = true ∨ evalClause assignment clause = true := by
            simpa [evalClause, evalLiteral, Bool.or_eq_true] using hEval
          rcases hcases with hi | htail
          · exact (hfalse hi).elim
          · exact ih htail
      | neg i =>
          intro hEval htrue
          have hcases : assignment i = false ∨ evalClause assignment clause = true := by
            simpa [evalClause, evalLiteral, Bool.or_eq_true] using hEval
          rcases hcases with hi | htail
          · change assignment i = true at htrue
            rw [hi] at htrue
            contradiction
          · exact ih htail

/-- A Boolean model of all clauses is a propositional model in the sense used
by `Sat.Fmla.proof`. -/
theorem satisfies_fmla_of_evalFmla_eq_true (assignment : ℕ → Bool)
    (fmla : Sat.Fmla) (h : evalFmla assignment fmla = true) :
    (boolValuation assignment).satisfies_fmla fmla := by
  constructor
  intro clause hclause
  apply satisfies_of_evalClause_eq_true assignment clause
  rw [evalFmla, List.all_eq_true] at h
  exact h clause hclause

/-- A kernel-checked LRAT refutation contradicts any executable Boolean model
of the same formula. -/
theorem false_of_lrat_and_evalFmla {fmla : Sat.Fmla}
    (hrefute : fmla.proof []) (assignment : ℕ → Bool)
    (h : evalFmla assignment fmla = true) : False :=
  hrefute (boolValuation assignment)
    (satisfies_fmla_of_evalFmla_eq_true assignment fmla h)

end SRG266.Search
