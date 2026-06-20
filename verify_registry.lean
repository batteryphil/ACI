import ACI_Governance.Root
import ACI_Governance.Node_2
import ACI_Governance.Node_3
import ACI_Governance.Node_4
import ACI_Governance.Node_5
import ACI_Governance.Node_6
import ACI_Governance.Node_7
import ACI_Governance.Node_8
import ACI_Governance.Node_9
import ACI_Governance.Node_10
open ACI_Governance

def check_node (n : Node) : IO Unit := 
  IO.println s!"NODE_ID: {n.id} | WEIGHT: {n.semantic_weight} | SEAL: {n.lattice_seal}"

def main : IO Unit := do
  check_node Node2
  check_node Node3
  check_node Node4
  check_node Node5
  check_node Node6
  check_node Node7
  check_node Node8
  check_node Node9
  check_node Node10
