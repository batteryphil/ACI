import subprocess
import os

def run_lean_proof(module_name):
    # Path construction: Assuming the file is in /root/my_project/proofs/
    # If your file is elsewhere, change the 'proofs' folder name below
    file_path = os.path.join("proofs", f"{module_name}.lean")
    
    # We use 'lean' directly with the file path to bypass Lake's module resolution errors
    # Lake env ensures the lean environment (mathlib/etc) is correctly loaded
    cmd = ["lake", "env", "lean", file_path]
    
    try:
        # Run with cwd set to project root to ensure imports resolve
        result = subprocess.run(cmd, cwd="/root/my_project", capture_output=True, text=True, check=True)
        return True, result.stdout
    except subprocess.CalledProcessError as e:
        return False, e.stderr

def execute_apex_synthesis(payload):
    proof_target = payload.get("proof_module")
    success, output = run_lean_proof(proof_target)
    
    if success:
        return f"LEAN_VERIFIED: {proof_target} compiled successfully."
    else:
        return f"LEAN_REJECTED: {output}"

