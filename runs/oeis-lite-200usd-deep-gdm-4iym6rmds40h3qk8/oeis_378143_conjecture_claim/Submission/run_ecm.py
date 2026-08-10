import subprocess
import multiprocessing
import sys
import os
import signal

sys.set_int_max_str_digits(100000)
val_str = str(10**(2**13) + 1)

def run_one_ecm(proc_id):
    # We will run ecm with B1=100000, and a random sigma
    # We pipe val_str to it
    # We use -sigma to set a random seed or just let ecm choose (ecm chooses randomly by default if no sigma is given)
    print(f"Process {proc_id} started")
    cmd = ["ecm", "100000"]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    stdout, stderr = proc.communicate(input=val_str)
    
    if "factor found" in stdout.lower() or "factor found" in stderr.lower():
        print(f"Process {proc_id} found something!")
        print(stdout)
        # Terminate all other processes
        os.kill(os.getpid(), signal.SIGKILL)
    else:
        print(f"Process {proc_id} finished without factor")

if __name__ == "__main__":
    sys.set_int_max_str_digits(100000)
    pool = multiprocessing.Pool(processes=32)
    pool.map(run_one_ecm, range(128))
