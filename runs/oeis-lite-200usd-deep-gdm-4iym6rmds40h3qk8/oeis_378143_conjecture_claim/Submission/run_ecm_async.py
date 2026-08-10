import subprocess
import sys
import os
import signal
import time

sys.set_int_max_str_digits(100000)
val_str = str(10**(2**13) + 1)

# We want to run many curves with B1=50000 or 100000
# Let us run them in parallel and monitor their output

def main():
    max_parallel = 32
    running = []
    curve_count = 0
    
    print("Starting parallel ECM search on 10^(2^13) + 1...", flush=True)
    
    while curve_count < 1000:
        # Check running processes
        still_running = []
        for proc, pid, cid in running:
            if proc.poll() is not None:
                # Process finished
                stdout = proc.stdout.read()
                stderr = proc.stderr.read()
                if "factor found" in stdout.lower() or "factor found" in stderr.lower():
                    print(f"!!! FACTOR FOUND in curve {cid} !!!", flush=True)
                    print(stdout, flush=True)
                    # Kill everything
                    os.killpg(os.getpgrp(), signal.SIGKILL)
                else:
                    # No factor found, just finish
                    print(f"Curve {cid} finished (no factor)", flush=True)
            else:
                still_running.append((proc, pid, cid))
        running = still_running
        
        # Start new ones if we have free slots
        while len(running) < max_parallel:
            curve_count += 1
            cmd = ["ecm", "100000"] # B1=100000
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, preexec_fn=os.setsid)
            # Write input immediately and close stdin so it starts
            proc.stdin.write(val_str + "\n")
            proc.stdin.close()
            running.append((proc, proc.pid, curve_count))
            print(f"Started curve {curve_count} (PID {proc.pid})", flush=True)
            
        time.sleep(1)

if __name__ == "__main__":
    main()
