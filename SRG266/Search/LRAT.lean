/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Tactic.Sat.FromLRAT

/-!
# Compact kernel checking of LRAT refutations

Mathlib's `lrat_proof` command turns a DIMACS formula and an LRAT trace into a
fully reified propositional tautology.  That is convenient for small SAT
instances, but the reified theorem has one `Prop` binder per DIMACS variable.
For the large finite certificates in this project we instead want to retain
the compact semantic statement produced internally by the checker:

```
Sat.Fmla.proof cnf []
```

This says directly that every valuation satisfying `cnf` satisfies the empty
clause, hence that `cnf` is unsatisfiable.  The command below is a deliberately
thin wrapper around Mathlib's LRAT proof builder.  It publishes both the parsed
CNF formula as `name.cnf` and the kernel-checked refutation as `name`.

The SAT solver is not trusted: it only generates LRAT data.  The theorem stored
in the environment is an ordinary proof term checked by the Lean kernel.
-/

open Lean

namespace SRG266.Search

open Mathlib.Tactic.Sat
open Std.Internal

/-- Add the compact LRAT theorem after the command elaborator has evaluated
its two string arguments.  If `expected` is absent, publish the parsed formula
as `name.cnf`; otherwise build the proof against the supplied formula.  In the
latter case Lean's declaration checker verifies that the supplied formula is
definitionally the DIMACS formula. -/
private def addLRATUnsat (name : Name) (cnfText lratText : String)
    (expected : Option Expr := none) : MetaM Unit := do
  let .success _ (_, clauses) := Parser.parseDimacs ⟨_, cnfText.startPos⟩
    | throwError "parse CNF failed"
  if clauses.isEmpty then
    throwError "empty CNF"
  let expanded := buildConj clauses 0 clauses.size
  let cnfExpr ← match expected with
    | some formula => pure formula
    | none =>
        let cnfName := name ++ `cnf
        addDecl <| Declaration.defnDecl {
          name := cnfName
          levelParams := []
          type := mkConst ``Sat.Fmla
          value := expanded
          hints := ReducibilityHints.regular 0
          safety := DefinitionSafety.safe
        }
        pure (mkConst cnfName)
  let .success _ steps := Parser.parseLRAT ⟨_, lratText.startPos⟩
    | throwError "parse LRAT failed"
  let proof ← buildProof clauses cnfExpr expanded steps
  addDecl <| Declaration.thmDecl {
    name
    levelParams := []
    type := mkApp2 (mkConst ``Sat.Fmla.proof) cnfExpr (buildClause #[])
    value := proof
  }

/--
`lrat_unsat name cnf lrat` defines

* `name.cnf : Sat.Fmla`, the parsed DIMACS formula; and
* `name : Sat.Fmla.proof name.cnf []`, its kernel-checked LRAT refutation.

Unlike Mathlib's `lrat_proof`, this command does not construct a proposition
with one binder for every DIMACS variable.
-/
elab "lrat_unsat " n:ident ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Lean.Elab.Command.liftTermElabM do
    let cnfText ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lratText ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    addLRATUnsat name cnfText lratText
    Lean.Elab.Term.addTermInfo' n (← mkConstWithLevelParams name)
      (isBinder := true) |>.run'

/--
`lrat_unsat_for name formula cnf lrat` checks the same LRAT certificate but
states the result directly for the Lean expression `formula`.  The declaration
is accepted only when `formula` is definitionally equal to the parsed DIMACS
formula, so an executable Lean CNF encoder can be the single source of truth for
both the mathematical soundness proof and the solver input.
-/
elab "lrat_unsat_for " n:ident ppSpace formula:term:max ppSpace cnf:term:max
    ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Lean.Elab.Command.liftTermElabM do
    let formulaExpr ← Lean.Elab.Term.elabTermEnsuringType formula (mkConst ``Sat.Fmla)
    let formulaExpr ← instantiateMVars formulaExpr
    let cnfText ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) cnf
    let lratText ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    addLRATUnsat name cnfText lratText (some formulaExpr)
    Lean.Elab.Term.addTermInfo' n (← mkConstWithLevelParams name)
      (isBinder := true) |>.run'

/-- Convert an evaluated SAT literal back to its one-based DIMACS spelling. -/
private def renderDIMACSLiteral : Sat.Literal → String
  | .pos index => toString (index + 1)
  | .neg index => "-" ++ toString (index + 1)

/-- Render an evaluated Lean formula as DIMACS.  This is elaborator input only;
the declaration checker still verifies the resulting proof against the
original formula expression. -/
private def renderDIMACSFormula (fmla : Sat.Fmla) : String :=
  let maximum := fmla.foldl (fun maximum clause =>
    clause.foldl (fun maximum literal =>
      let index := match literal with
        | .pos i => i + 1
        | .neg i => i + 1
      max maximum index) maximum) 0
  let clauses := fmla.map fun clause =>
    String.intercalate " " (clause.map renderDIMACSLiteral) ++
      (if clause.isEmpty then "0\n" else " 0\n")
  "p cnf " ++ toString maximum ++ " " ++ toString fmla.length ++ "\n" ++
    String.join clauses

/--
`lrat_unsat_for_computed name formula lrat` evaluates the concrete Lean CNF to
obtain its DIMACS clause array, then checks `lrat` exactly as
`lrat_unsat_for` does.  No generated `.cnf` file is needed, and unsafe
elaboration cannot establish a false theorem because the final proof term is
kernel-checked at type `formula.proof []`.
-/
elab "lrat_unsat_for_computed " n:ident ppSpace formula:term:max ppSpace
    lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Lean.Elab.Command.liftTermElabM do
    let formulaExpr ← Lean.Elab.Term.elabTermEnsuringType formula (mkConst ``Sat.Fmla)
    let formulaExpr ← instantiateMVars formulaExpr
    let formulaValue ← unsafe Lean.Elab.Term.evalTerm Sat.Fmla
      (mkConst ``Sat.Fmla) formula
    let lratText ← unsafe Lean.Elab.Term.evalTerm String (mkConst ``String) lrat
    addLRATUnsat name (renderDIMACSFormula formulaValue) lratText (some formulaExpr)
    Lean.Elab.Term.addTermInfo' n (← mkConstWithLevelParams name)
      (isBinder := true) |>.run'

end SRG266.Search
