import os
import json
import time

def analyze_blockages():
    print("[STAGE 1] Scanning Architecture for Operational Blockages...")
    
    # Files to audit
    failed_file = "failed_targets.txt"
    log_file = "system_blockage_report.log"
    untracked_file = "untracked_files.txt"
    
    analysis = {
        "timestamp": time.time(),
        "failed_targets": [],
        "blockage_logs_detected": 0,
        "untracked_modules": [],
        "critical_path_priority": []
    }
    
    # 1. Parse failed targets
    if os.path.exists(failed_file):
        with open(failed_file, "r") as f:
            analysis["failed_targets"] = [line.strip() for line in f if line.strip()]
            
    # 2. Check blockage reports
    if os.path.exists(log_file):
        with open(log_file, "r") as f:
            log_lines = f.readlines()
            analysis["blockage_logs_detected"] = len(log_lines)
            
    # 3. Parse untracked files that might break downstream dependencies
    if os.path.exists(untracked_file):
        with open(untracked_file, "r") as f:
            analysis["untracked_modules"] = [line.strip() for line in f if line.strip().endswith('.lean')]

    # 4. Generate Priority Vector (Targeting core dependencies first)
    # Core architectural modules are prioritized to unblock dependent physics modules
    core_keywords = ["Core", "Main", "Governor", "Sovereign", "Verify", "Logic"]
    for target in analysis["failed_targets"]:
        if any(kw in target for kw in core_keywords):
            analysis["critical_path_priority"].append({"module": target, "tier": "CRITICAL_CORE"})
        else:
            analysis["critical_path_priority"].append({"module": target, "tier": "STANDARD_LEAF"})
            
    print(f" -> Found {len(analysis['failed_targets'])} failed verification targets.")
    print(f" -> Isolated {len(analysis['untracked_modules'])} untracked Lean files.")
    print(f" -> Logged {analysis['blockage_logs_detected']} systemic blockage entries.")
    return analysis

def export_at2_resolution_matrix(matrix):
    print("\n[STAGE 2] Serializing AT2 Bottleneck Resolution Matrix...")
    export_path = "at2_bottleneck_matrix.json"
    
    with open(export_path, "w") as f:
        json.dump(matrix, f, indent=2)
        
    print(f" -> Resolution roadmap exported to: {export_path}")
    
    # Display the top priority files that need to be pushed to the CI next
    print("\n[CRITICAL PATH RECOMMENDATIONS FOR UPSTREAM CI]")
    criticals = [m["module"] for m in matrix["critical_path_priority"] if m["tier"] == "CRITICAL_CORE"]
    if criticals:
        for c in criticals[:5]:
            print(f"   [*] High Priority Handoff: {c}")
    else:
        print("   [-] No immediate core blockages detected. Focus on leaf modules.")

if __name__ == "__main__":
    print("==============================================")
    print("     BEGINNING AT2: BOTTLENECK RESOLUTION    ")
    print("==============================================")
    
    resolution_matrix = analyze_blockages()
    export_at2_resolution_matrix(resolution_matrix)
    
    print("==============================================")
    print("           AT2 SUITE SUCCEEDED                ")
    print("==============================================")
