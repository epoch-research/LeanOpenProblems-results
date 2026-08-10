import itertools

def search():
    # We want to find a set of queries X_1, ..., X_n.
    # Each X_i is a boolean function of (p0, d_0, d_1, ..., d_{i-1}),
    # where p0 is P, d_0 is the decision of P, and d_i is the decision of X_i.
    # We want that for every assignment of (d_0, d_1, ..., d_n) in {0, 1}^(n+1):
    #   The set of satisfying p0 for the constraints:
    #     d_0 == p0
    #     d_1 == X_1(p0, d_0)
    #     ...
    #     d_n == X_n(p0, d_0, ..., d_{n-1})
    #   is either empty (meaning the branch is inconsistent, so we can prove False),
    #   or is {1} (meaning we can prove P).
    # In other words, there is NO assignment of (d_0, d_1, ..., d_n) where p0 = 0 is a valid solution.
    
    # Let's search for n up to 3.
    # For n=1: we have p0, d_0.
    # X_1 is a function of (p0, d_0). There are 2^4 = 16 such functions.
    # For each such function, let's check if the condition holds.
    
    print("Searching for n=1...")
    for f1_val in range(16):
        # f1_val represents the truth table of X_1(p0, d_0)
        # inputs are (p0, d_0) in [(0,0), (0,1), (1,0), (1,1)]
        X_1 = lambda p0, d_0, val=f1_val: (val >> (p0 * 2 + d_0)) & 1
        
        # Check if there is any (d_0, d_1) where p0 = 0 is satisfying.
        has_bad_branch = False
        for d_0, d_1 in itertools.product([0, 1], repeat=2):
            # Check if p0 = 0 is a solution
            p0 = 0
            cond0 = (d_0 == p0)
            cond1 = (d_1 == X_1(p0, d_0))
            if cond0 and cond1:
                # This branch has a solution with p0 = 0, so it's a bad branch
                has_bad_branch = True
                break
        if not has_bad_branch:
            print(f"Found for n=1! Truth table of X_1: {bin(f1_val)}")
            return
            
    print("Searching for n=2...")
    # For n=2, X_1 is a function of (p0, d_0) (16 options).
    # X_2 is a function of (p0, d_0, d_1) (2^8 = 256 options).
    for f1_val in range(16):
        X_1 = lambda p0, d_0, val=f1_val: (val >> (p0 * 2 + d_0)) & 1
        for f2_val in range(256):
            X_2 = lambda p0, d_0, d_1, val=f2_val: (val >> (p0 * 4 + d_0 * 2 + d_1)) & 1
            
            has_bad_branch = False
            for d_0, d_1, d_2 in itertools.product([0, 1], repeat=3):
                p0 = 0
                cond0 = (d_0 == p0)
                cond1 = (d_1 == X_1(p0, d_0))
                cond2 = (d_2 == X_2(p0, d_0, d_1))
                if cond0 and cond1 and cond2:
                    has_bad_branch = True
                    break
            if not has_bad_branch:
                print(f"Found for n=2!")
                print(f"X_1 table: {bin(f1_val)}")
                print(f"X_2 table: {bin(f2_val)}")
                # Print the definition of X_1 and X_2
                for p0, d_0 in itertools.product([0, 1], repeat=2):
                    print(f"  X_1({p0}, {d_0}) = {X_1(p0, d_0)}")
                for p0, d_0, d_1 in itertools.product([0, 1], repeat=3):
                    print(f"  X_2({p0}, {d_0}, {d_1}) = {X_2(p0, d_0, d_1)}")
                return

    print("No solution found for n <= 2.")

search()
