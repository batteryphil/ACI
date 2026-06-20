#!/bin/bash

# Clear existing nodes to avoid stale artifacts
rm ACI_Governance/Node_*.lean

for i in {2..10}; do
    cat << EOF2 > "ACI_Governance/Node_${i}.lean"
namespace ACI_Governance
import ACI_Governance.Root

def Node${i} : Node := { 
    id := ${i}, 
    semantic_weight := 1.0, 
    is_unified := true, 
    lattice_seal := "SEALED_VALID" 
}
end ACI_Governance
EOF2
done

# Build the entire library as one unit
lake build
