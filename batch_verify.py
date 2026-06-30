import os
from Governor import submit_task

proof_dir = "/root/my_project/proofs"

# Check if directory exists
if os.path.exists(proof_dir):
    for file in os.listdir(proof_dir):
        if file.endswith(".lean"):
            module = file.replace(".lean", "")
            task = {"type": "LeanProof", "payload": {"proof_module": module}}
            print(f"Verifying {module}: {submit_task(task)}")
else:
    print(f"Directory {proof_dir} not found.")

