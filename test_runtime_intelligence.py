import sys
import numpy as np
from PrimeRuntimeV4_backup import (
    mc2_effective_mass,
    mc2_coupling_strength,
    n7_gate_decision,
    H_OPT7
)

def execute_intelligence_audit():
    print("=== START RUNTIME INTELLIGENCE AUDIT ===")
    
    # Test 1: Asymptotic Mass Behavior near MC2_U_MAX (0.95)
    m_base = 2.0
    load_nominal = 0.50
    load_critical = 0.94
    
    m_eff_nominal = mc2_effective_mass(m_base, load_nominal)
    m_eff_critical = mc2_effective_mass(m_base, load_critical)
    
    print(f"MASS_NOMINAL:{m_eff_nominal:.4f}")
    print(f"MASS_CRITICAL:{m_eff_critical:.4f}")
    
    # Check for core mathematical inversion bug
    if m_eff_critical <= m_eff_nominal:
        print("FAIL:MASS_INVERSION")
        sys.exit(1)
        
    # Test 2: Symmetric Reciprocity Under Parameter Scaling
    m_a, m_b = 1.5, 4.5
    c_ab = mc2_coupling_strength(m_a, m_b)
    c_ba = mc2_coupling_strength(m_b, m_a)
    
    print(f"COUPLING_AB:{c_ab:.6f}")
    print(f"COUPLING_BA:{c_ba:.6f}")
    if abs(c_ab - c_ba) > 1e-12:
        print("FAIL:ASYMMETRIC_TOPOLOGY")
        sys.exit(1)
        
    # Test 3: Gate Isolation Under High Stress States
    mock_margins = [0.91, 0.85, 0.12, 0.76, 0.99]
    floor_val = 0.50
    status, index = n7_gate_decision(mock_margins, floor_val)
    
    print(f"GATE_STATUS:{status}")
    print(f"ISOLATED_THREAT_INDEX:{index}")
    if status != "Vetoed" or index != 2:
        print("FAIL:GATE_BYPASS")
        sys.exit(1)
        
    # Test 4: Hamiltonian Zero Momentum Phase Space Baseline
    p_vector = np.zeros(7)
    m_vector = np.ones(7)
    k_scalar = 1.0
    y_act = np.array([2.0] * 7)
    y_spn = np.array([2.0] * 7)
    W, A, dl = 1.0, np.ones(7), np.zeros(7)
    
    h_val = H_OPT7(p_vector, m_vector, k_scalar, y_act, y_spn, W, A, dl)
    print(f"HAMILTONIAN_BASELINE:{h_val:.4f}")
    if abs(h_val) > 1e-12:
        print("FAIL:ENERGY_LEAK_IN_STATIC_STATE")
        sys.exit(1)
        
    print("SYSTEM_INTELLIGENCE:FULLY_COMPLIANT")
    sys.exit(0)

if __name__ == "__main__":
    execute_intelligence_audit()

