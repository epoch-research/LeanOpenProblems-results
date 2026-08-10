import re

def optimize():
    with open("/workspace/leanproject/Submission/Spec.lean.tmp", "r") as f:
        content = f.read()

    # We want to find all theorems and process their proofs.
    # The theorems are:
    # oeis_A237720_conjecture_ii_block_50, block_100, ..., block_561
    
    # Let us find each theorem definition and its proof.
    # A theorem looks like:
    # theorem oeis_A237720_conjecture_ii_block_XYZ ... :
    #     ∃ p, ... := by
    #   rcases ...
    #   (lots of cases)
    #
    # We can split the content by "theorem "
    parts = content.split("theorem ")
    new_parts = [parts[0]]
    
    for part in parts[1:]:
        # check if this is one of our block theorems
        match = re.match(r"(oeis_A237720_conjecture_ii_block_\d+)\s+(.*?)\s*:\n\s*(.*?)\s*:=\s*by\s*(.*)", part, re.DOTALL)
        if match:
            name = match.group(1)
            args = match.group(2)
            type_str = match.group(3)
            proof_body = match.group(4)
            
            # Now we parse the proof_body.
            # We want to extract only the lines that look like:
            #   · use P
            #     have h_sqrt : _root_.Nat.sqrt (N + P) = Q := by norm_num
            #     refine ⟨by decide, by decide, ?_⟩
            #     rw [h_sqrt]
            #     decide
            #
            # Let us split proof_body by "· "
            cases = proof_body.split("· ")
            new_cases = []
            for case in cases[1:]:
                # Check if it is a "use" case or a dummy case (contradiction / omega)
                if "use " in case:
                    # Keep this case!
                    # Clean up trailing spaces or newlines
                    new_cases.append("  · " + case.strip())
                elif "omega" in case or "contradiction" in case:
                    # Ignore dummy cases!
                    pass
            
            # Reconstruct the proof using interval_cases n
            new_proof = "  interval_cases n\n" + "\n".join(new_cases)
            
            # Reconstruct the part
            new_part = f"{name} {args} :\n    {type_str} := by\n{new_proof}\n\n"
            new_parts.append(new_part)
        else:
            # Not a block theorem, keep as is
            new_parts.append(part)
            
    optimized_content = "theorem ".join(new_parts)
    
    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write(optimized_content)
    print("Optimization completed!")

if __name__ == '__main__':
    optimize()
