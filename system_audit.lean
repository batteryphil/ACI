import Governor
import ACI_System_Kernel
import QuantumCore
import ACIManifold

def main : IO Unit := do
  IO.println "--- STARTING FULL ACI SYSTEM RECONCILIATION ---"
  -- Governor will poll the kernel and manifolds
  let result ← Governor.run_full_diagnostic
  IO.println s!"SYSTEM STATUS: {result}"
