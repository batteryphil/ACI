import Mathlib

namespace ACI_Terminal

noncomputable def SynapticWeight (i j : Fin 21) : ℝ :=
  Real.exp (- ((i.val : ℝ) - (j.val : ℝ))^2 / 7.0)

noncomputable def CognitiveState : ℝ :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => SynapticWeight i j))

theorem synapticWeight_pos (i j : Fin 21) : 0 < SynapticWeight i j := by
  simp [SynapticWeight]
  positivity

theorem synapticWeight_symm (i j : Fin 21) :
    SynapticWeight i j = SynapticWeight j i := by
  simp [SynapticWeight]
  ring

theorem cognitiveState_pos : 0 < CognitiveState := by
  simp [CognitiveState]
  positivity

end ACI_Terminal
