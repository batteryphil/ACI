import json
import os
import time

def stage_apex_assets():
    print("==============================================")
    print("     BEGINNING AT3: INTEGRATION PREPARATION   ")
    print("==============================================")
    
    matrix_path = "at2_bottleneck_matrix.json"
    if not os.path.exists(matrix_path):
        print(" -> Error: AT2 resolution matrix missing. Run at2_bottleneck_resolver.py first.")
        return
        
    with open(matrix_path, "r") as f:
        matrix = json.load(f)
        
    print("[STAGE 1] Extracting Bottleneck Priorities...")
    untracked = matrix.get("untracked_modules", [])
    priorities = matrix.get("critical_path_priority", [])
    critical_targets = [p["module"] for p in priorities if p["tier"] == "CRITICAL_CORE"]
    
    handoff_manifest = {
        "suite": "AT3",
        "timestamp": time.time(),
        "primary_unresolved_core": critical_targets if critical_targets else ["None"],
        "files_to_track_locally": untracked,
        "total_targets_flagged": len(matrix.get("failed_targets", []))
    }
    
    export_path = "at3_integration_package.json"
    with open(export_path, "w") as f:
        json.dump(handoff_manifest, f, indent=2)
        
    print(f" -> Staging report successfully generated: {export_path}")
    print("==============================================")

if __name__ == "__main__":
    stage_apex_assets()
