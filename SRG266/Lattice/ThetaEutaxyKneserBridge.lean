/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.OrderFourGlueVector
import SRG266.Lattice.KneserBoundary
import SRG266.Lattice.NormTwoADEDecomposition

/-!
# The theta-eutaxy bypass connected to host normalization

This small module composes the lightweight theta/ADE result with the already
proved frame-complement descent.  It stops at
`Rank15PreEnumerationNormalizationInput`, immediately before the large checked
shell enumerations, so rebuilding the lattice argument does not schedule those
certificate chunks.
-/

namespace SRG266

universe u

/-- The theta/ADE and full-rank glue inputs imply the rooted norm-one-free
classification consumed by the graph-specific host reduction. -/
theorem rootedNormOneFreeClassification_of_thetaEutaxy_glue
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hD12 : D12FullRankGlueRigidityInput)
    (hE7E7 : E7E7FullRankGlueRigidityInput)
    (hA15 : A15FullRankGlueRigidityInput) :
    RootedNormOneFreeClassification :=
  rootedNormOneFreeClassification_of_corankFour
    (rootedCorankFourClassification_of_thetaEutaxy_glue
      hTheta hD12 hE7E7 hA15)

/-- The complete lightweight implication chain up to the boundary consumed by
the checked host enumerations. -/
theorem rank15PreEnumerationNormalization_of_thetaEutaxy_glue
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hD12 : D12FullRankGlueRigidityInput)
    (hE7E7 : E7E7FullRankGlueRigidityInput)
    (hA15 : A15FullRankGlueRigidityInput) :
    Rank15PreEnumerationNormalizationInput.{u} :=
  rank15PreEnumerationNormalization_of_corankFour
    (rootedCorankFourClassification_of_thetaEutaxy_glue
      hTheta hD12 hE7E7 hA15)

/-- Each host branch reduces coordinate rigidity to one normalized divisibility
witness in the ambient lattice. -/
theorem rank15PreEnumerationNormalization_of_thetaEutaxy_glueVectors
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hD12 : D12NormalizedGlueVectorInput)
    (hE7E7 : E7E7NormalizedGlueVectorInput)
    (hA15 : A15NormalizedGlueVectorInput) :
    Rank15PreEnumerationNormalizationInput.{u} :=
  rank15PreEnumerationNormalization_of_corankFour
    (rootedCorankFourClassification_of_thetaEutaxy_glueVectors
      hTheta hD12 hE7E7 hA15)

/-- The theta/ADE structural input implies the rooted norm-one-free
classification through the three full-rank overlattice calculations. -/
theorem rootedNormOneFreeClassification_of_thetaEutaxy
    (hTheta : ThetaEutacticADEDecompositionInput) :
    RootedNormOneFreeClassification :=
  rootedNormOneFreeClassification_of_corankFour
    (Lattice.rootedCorankFourClassification_of_thetaEutaxy hTheta)

/-- The complete implication chain from theta/ADE to the exact normalization
boundary consumed by the checked host enumerations, with no lattice
classification or full-rank glue input. -/
theorem rank15PreEnumerationNormalization_of_thetaEutaxy
    (hTheta : ThetaEutacticADEDecompositionInput) :
    Rank15PreEnumerationNormalizationInput.{u} :=
  rank15PreEnumerationNormalization_of_corankFour
    (Lattice.rootedCorankFourClassification_of_thetaEutaxy hTheta)

/-- Root eutaxy implies the rooted norm-one-free classification. The finite ADE
classification is supplied by
`thetaEutacticADEDecomposition_of_rootEutaxy`. -/
theorem rootedNormOneFreeClassification_of_rootEutaxy
    (hTheta : ThetaRootEutaxyInput) :
    RootedNormOneFreeClassification :=
  rootedNormOneFreeClassification_of_thetaEutaxy
    (thetaEutacticADEDecomposition_of_rootEutaxy hTheta)

/-- Root eutaxy implies host normalization without an ADE-classification
hypothesis. -/
theorem rank15PreEnumerationNormalization_of_rootEutaxy
    (hTheta : ThetaRootEutaxyInput) :
    Rank15PreEnumerationNormalizationInput.{u} :=
  rank15PreEnumerationNormalization_of_thetaEutaxy
    (thetaEutacticADEDecomposition_of_rootEutaxy hTheta)

end SRG266
