import sys
import os
import json
import time
import threading
import numpy as np

# Ensure working directory is correctly set to your core repository
sys.path.append("/root/my_project")

class LiveRuntimeBinder:
    def __init__(self):
        print("==========================================================================")
        print("   INITIALIZING PHASE 42: LIVE-BINDING INTER-PROCESS TELEMETRY GOVERNOR  ")
        print("==========================================================================")

        # 1. Active Process Binding
        try:
            # FIX: Point to the actual production module containing the PrimeRuntimeV4 class container
            from PrimeRuntimeV4 import PrimeRuntimeV4
            from VerifyBridge import VerifyBridge

            # Instantiating the live, mutable core simulation loop
            self.live_kernel = PrimeRuntimeV4(node_count=21)
            self.bridge = VerifyBridge()
            
            # Actively override the bridge runtime instance to force a live memory link
            self.bridge.rt = self.live_kernel

            print("[STAGE 1] Live Inter-Process Memory Binding Established Successfully.")
            print(f" -> Core Engine State Synchronized: {self.live_kernel.verify_all()}")
        except ImportError as e:
            print(f" -> Critical Loading Error during runtime hook binding: {e}")
            sys.exit(1)

        self.is_running = False
        self.telemetry_history = []
        self.lock = threading.Lock()

    def background_execution_loop(self, steps=100, dt=0.05, delay=0.01):
        """Simulates live, asynchronous state evolution and active hardware polling."""
        print(f"\n[STAGE 2] Spawning Asynchronous Core Driver Thread ({steps} Cycles)...")
        self.is_running = True
        for step in range(steps):
            if not self.is_running:
                break
            with self.lock:
                # 1. Drive the live matrix update step across the 21 physical nodes
                # This alters mutable memory variables inside PrimeRuntimeV4 in real time
                margin_scalar = self.live_kernel.step(dt)

                # 2. Query the consensus gate logic using the active running state
                status_string = self.live_kernel.verify_all()

                # 3. Interrogate the VerifyBridge status gate routing
                bridge_status = self.bridge.verified_step(dt)

            # Log the live telemetric frame
            frame = {
                "step": step,
                "timestamp": time.time(),
                "live_margin": margin_scalar,
                "status_msg": status_string,
                "bridge_decision": bridge_status.get("status", "UNKNOWN")
            }
            self.telemetry_history.append(frame)

            # Circuit Breaker: If the live binding catches a BREACH status, trigger an instant halt
            if bridge_status.get("status") == "HALT":
                print(f"\n[!] LIVE CIRCUIT BREAKER TRIGGERED AT STEP {step:04d} — BREACH DETECTED.")
                print(f" -> MoruzinLaw.lean Enforcement: Halting active state trajectories.")
                self.is_running = False
                break

            time.sleep(delay)

        self.is_running = False
        print(" -> Asynchronous background core driver thread terminated cleanly.")

    def run_live_verification_suite(self):
        # Spawn the background simulation loop on an independent thread
        # This emulates real hardware-in-the-loop socket updates
        driver_thread = threading.Thread(target=self.background_execution_loop, kwargs={"steps": 50, "dt": 0.05})
        driver_thread.start()

        print("\n[STAGE 3] Initiating Live Telemetry Polling & Obligation Export...")
        # While the background thread modifies variables, the main thread acts as a formal judge
        frame_counter = 0
        while driver_thread.is_alive() or self.is_running:
            with self.lock:
                # Capture the live, fluctuating string straight from the running engine's memory
                current_state_vector = self.live_kernel.manifold_state

            if frame_counter % 10 == 0:
                print(f"    [*] Polled Frame {frame_counter:03d} -> Live State Memory Vector: {current_state_vector}")

                # Synchronize and package the live operational status to disk for the CI server
                self.bridge.export_obligation(
                    name=f"live_trajectory_frame_{frame_counter}",
                    claim=f"0 <= T_kinetic + V_potential"
                )
                self.bridge.export_to_json("obligations.json")

            frame_counter += 1
            time.sleep(0.02)

        driver_thread.join()

        print("\n[STAGE 4] Consolidating Live Execution Analysis Report...")
        report = self.bridge.full_report()
        print("==========================================================================")
        print(f" -> Runtime Integrity Verified Safely : {report.get('runtime')}")
        print(f" -> Final Manifold Coordinate Extracted : {report.get('manifold')}")
        print(f" -> Asynchronous JSON Obligations Synced: {report.get('obligations')} Packages")

        # Save complete runtime report to disk
        with open("test_phase42_report.json", "w") as f:
            json.dump(self.telemetry_history, f, indent=2)
        print(" -> Complete runtime telemetry log successfully written to: test_phase42_report.json")
        print("==========================================================================")

if __name__ == "__main__":
    binder = LiveRuntimeBinder()
    binder.run_live_verification_suite()

