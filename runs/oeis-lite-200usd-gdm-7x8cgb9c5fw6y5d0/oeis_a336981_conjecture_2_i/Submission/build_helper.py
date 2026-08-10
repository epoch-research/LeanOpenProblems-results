import subprocess
import re
import sys
import os

def compile_file(lean_path, olean_path):
    print(f"Compiling {lean_path} -> {olean_path}")
    # Create directory if it doesn't exist
    os.makedirs(os.path.dirname(olean_path), exist_ok=True)
    cmd = ["lake", "env", "lean", lean_path, "-o", olean_path]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        print(f"Failed to compile {lean_path}:")
        print(res.stdout)
        print(res.stderr)
        return False, res.stdout + "\n" + res.stderr
    return True, ""

def main():
    target = "FormalConjectures/Util/ProblemImports.lean"
    target_olean = ".lake/build/lib/lean/FormalConjectures/Util/ProblemImports.olean"
    
    # We will loop until ProblemImports compiles successfully
    for iteration in range(500):
        print(f"\n--- Iteration {iteration} ---")
        cmd = ["lake", "env", "lean", target, "-o", target_olean]
        res = subprocess.run(cmd, capture_output=True, text=True)
        if res.returncode == 0:
            print("Successfully compiled ProblemImports.lean!")
            sys.exit(0)
            
        # Parse the error message
        # Example error: "object file '/workspace/leanproject/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Category/ModuleCat/Ext/HasExt.olean' of module Mathlib.Algebra.Category.ModuleCat.Ext.HasExt does not exist"
        err = res.stdout + "\n" + res.stderr
        match = re.search(r"object file '([^']+)' of module ([^ ]+) does not exist", err)
        if not match:
            print("Unknown error:")
            print(err)
            sys.exit(1)
            
        missing_olean = match.group(1)
        missing_module = match.group(2)
        
        # Determine the source .lean file
        # If the module starts with Mathlib., it is in the mathlib package
        if missing_module == "Mathlib":
            src_lean = ".lake/packages/mathlib/Mathlib.lean"
        elif missing_module.startswith("Mathlib."):
            rel_path = missing_module.replace(".", "/") + ".lean"
            src_lean = os.path.join(".lake/packages/mathlib", rel_path)
        elif missing_module.startswith("FormalConjecturesForMathlib."):
            rel_path = missing_module.replace(".", "/") + ".lean"
            src_lean = rel_path
        elif missing_module.startswith("FormalConjectures."):
            rel_path = missing_module.replace(".", "/") + ".lean"
            src_lean = rel_path
        else:
            print(f"Unknown module source for {missing_module}")
            sys.exit(1)
            
        if not os.path.exists(src_lean):
            print(f"Source file {src_lean} does not exist!")
            sys.exit(1)
            
        success, compile_err = compile_file(src_lean, missing_olean)
        if not success:
            # If compiling the missing file itself failed due to a missing dependency,
            # we will just continue the loop because the next iteration will detect the dependency of THAT file!
            # Wait, let's parse the dependency of THAT file from the error message.
            match2 = re.search(r"object file '([^']+)' of module ([^ ]+) does not exist", compile_err)
            if match2:
                missing_olean = match2.group(1)
                missing_module = match2.group(2)
                if missing_module == "Mathlib":
                    src_lean = ".lake/packages/mathlib/Mathlib.lean"
                elif missing_module.startswith("Mathlib."):
                    rel_path = missing_module.replace(".", "/") + ".lean"
                    src_lean = os.path.join(".lake/packages/mathlib", rel_path)
                elif missing_module.startswith("FormalConjecturesForMathlib."):
                    rel_path = missing_module.replace(".", "/") + ".lean"
                    src_lean = rel_path
                elif missing_module.startswith("FormalConjectures."):
                    rel_path = missing_module.replace(".", "/") + ".lean"
                    src_lean = rel_path
                else:
                    print("Could not resolve nested dependency")
                    sys.exit(1)
                
                print(f"Nested dependency missing: {src_lean}")
                # We will let the loop try to build this nested dependency in the next iteration.
            else:
                print(f"Failed to compile {src_lean} due to other errors.")
                sys.exit(1)

if __name__ == '__main__':
    main()
