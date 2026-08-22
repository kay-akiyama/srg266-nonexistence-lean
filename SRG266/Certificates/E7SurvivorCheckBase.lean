/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7WeylTransport

/-!
# Reduced checks for E7 survivor witnesses

This module checks the serialized fields, the two 56-weight divisibility
conditions, and the five canonical shell cardinalities separately.
-/

namespace SRG266

def e7ResidualExpectedEligibleCount : E7ResidualType → ℕ
  | .twoTen => 160
  | .fourEightGeneric => 146
  | .fourEightSpecial => 192
  | .sixGenericSixGeneric => 144
  | .sixGenericSixSpecial => 182

def e7ResidualCanonicalEligibleCount (kind : E7ResidualType) : ℕ :=
  Fintype.card (E7ResidualEligibleIndex
    (e7ResidualCanonical kind).1 (e7ResidualCanonical kind).2)

def E7SurvivorOrbitCertificate.centroidTransportFactorAudit
    (c : E7SurvivorOrbitCertificate) : Bool :=
  decide (
    (∀ w : E7WeightIndex,
      integerDot (fun i => c.y₁ i / 5) (e7Weight4 w) % 8 = 0) ∧
    (∀ w : E7WeightIndex,
      integerDot (fun i => c.y₂ i / 5) (e7Weight4 w) % 8 = 0))

/-- The serialized fields, using the declared canonical eligible-shell
count. -/
def E7SurvivorOrbitCertificate.coreAudit
    (c : E7SurvivorOrbitCertificate) : Bool :=
  let canonical := e7ResidualCanonical c.residualType
  let target₁ := if c.swapFactors then canonical.2 else canonical.1
  let target₂ := if c.swapFactors then canonical.1 else canonical.2
  decide (
    (∀ i, c.y₁ i % 5 = 0) ∧
    (∀ i, c.y₂ i % 5 = 0) ∧
    c.reportedEligible =
      e7ResidualExpectedEligibleCount c.residualType ∧
    e7ApplyReflections (fun i => c.y₁ i / 5) c.leftReflections =
      some target₁ ∧
    e7ApplyReflections (fun i => c.y₂ i / 5) c.rightReflections =
      some target₂)

def E7SurvivorOrbitCertificate.transportRootAudit
    (c : E7SurvivorOrbitCertificate) : Bool :=
  c.leftReflections.all e7ReflectionTransportCheck &&
    c.rightReflections.all e7ReflectionTransportCheck

end SRG266
