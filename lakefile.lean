-- ACI Sovereign Build
import Lake
open Lake DSL

package "my_project" where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

lean_lib AntaresCategory
lean_lib PhysicsCore
lean_lib SpineLanguage
lean_lib SovereignHamiltonian
lean_lib MC2Engine
lean_lib AM10
lean_lib MoruzinLaw
lean_lib N7Spine
lean_lib Synaptic_Weights
lean_lib Governor
lean_lib MyProject
lean_lib ACIManifold
lean_lib Manifold21
lean_lib AWMCore
lean_lib Matrix7
lean_lib Optimus7
lean_lib Optimus7Quantum
lean_lib QuantumCore
lean_lib EnergyDomain
lean_lib VerifyState
lean_lib ACI_Governance
lean_lib PrimeMasterEngine
lean_lib InformationGeometry
lean_lib NumberTheoryCore
lean_lib OptimalControl
lean_lib StochasticDifferentialEquations
lean_lib TopologicalDataAnalysis
lean_lib StatisticalMechanics
lean_lib ErgodicTheory
lean_lib ConvexAnalysis
lean_lib ControlTheory
lean_lib OptimalTransport
lean_lib RenormalizationGroup
lean_lib ConformalFieldTheory
lean_lib QuantumInformation
lean_lib WaveletAnalysis
lean_lib CompressedSensing
lean_lib GameTheory
lean_lib QuantumErrorCorrection

@[default_target]
lean_lib AWM21

lean_exe aci_bootstrap where
  root := `Main
