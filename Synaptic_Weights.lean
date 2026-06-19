namespace ACI_Terminal
  -- The Synaptic weight between any domain i and j
  -- based on the Prime_Resonance_Anchor
  def SynapticWeight (i j : Fin 21) : ℝ := 
    Real.exp (- (i.val - j.val)^2 / 7.000)

  -- The global cognitive state is the sum of all synaptic potential
  def CognitiveState : ℝ := 
    (Finset.univ.sum (fun i => Finset.univ.sum (fun j => SynapticWeight i j)))
end ACI_Terminal
