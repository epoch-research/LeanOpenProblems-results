def find_proof_tree():
    # We represent propositions as strings or objects.
    # Initially we have 1.
    # We want to prove 0.
    # At each step we can query get_p_cheat on any proposition P in our language.
    # If we query P:
    #   val branch: we gain P
    #   not_val branch: we gain P -> False (written as ¬P)
    
    # We can simplify propositions to keep the language small:
    # 0, 1, 1->0, ¬(1->0), ¬0, ¬1, 0->1, ¬(0->1), 0=1, ¬(0=1)
    # Let's write down the exact types and how we can get False.
    
    # A state is a set of known propositions.
    # A known proposition can be:
    # '0': G_prop n 0
    # '1': G_prop (n-1) 0 (always known!)
    # '¬0': 0 -> False
    # '¬1': 1 -> False
    # '1->0': 1 -> 0
    # '¬(1->0)': (1 -> 0) -> False
    # '0->1': 0 -> 1
    # '¬(0->1)': (0 -> 1) -> False
    # '0=1': 0 = 1 (equivalent to (0->1) and (1->0))
    # '¬(0=1)': (0 = 1) -> False
    # '¬¬(1->0)': ((1->0)->False)->False
    
    # Let's write a function to check if a state is winning:
    def is_winning(state):
        if '0' in state:
            return True
        # If we have both X and ¬X, we can prove False, which can prove 0.
        for x in list(state):
            if x == '1' and '¬1' in state:
                return True
            if x == '0' and '¬0' in state:
                return True
            if x == '1->0' and '¬(1->0)' in state:
                return True
            if x == '0->1' and '¬(0->1)' in state:
                return True
            if x == '0=1' and '¬(0=1)' in state:
                return True
            if x == '¬(1->0)' and '¬¬(1->0)' in state:
                return True
        return False

    memo = {}

    def solve(state, max_depth, matched_so_far):
        # Normalize state:
        # Since '1' is always known, add '1'.
        state = state | frozenset(['1'])
        
        # Deductions:
        # If we have '1' and '1->0', we get '0'.
        if '1->0' in state and '1' in state:
            state = state | frozenset(['0'])
        # If we have '0' and '0->1', we get '1'.
        if '0' in state and '0->1' in state:
            state = state | frozenset(['1'])
        # If we have '0=1', we get '0->1' and '1->0'.
        if '0=1' in state:
            state = state | frozenset(['0->1', '1->0'])
        # If we have '0->1' and '1->0', we get '0=1'.
        if '0->1' in state and '1->0' in state:
            state = state | frozenset(['0=1'])
        # If we have '0', we can prove '1->0' (by fun _ => 0).
        if '0' in state:
            state = state | frozenset(['1->0'])
        # If we have '1', we can prove '0->1' (by fun _ => 1).
        if '1' in state:
            state = state | frozenset(['0->1'])
        # If we have '¬0', we can prove '0->1' (by fun h0 => False.elim (¬0 h0)).
        if '¬0' in state:
            state = state | frozenset(['0->1'])
        # If we have '¬1', we can prove '1->0' (by fun h1 => False.elim (¬1 h1)).
        if '¬1' in state:
            state = state | frozenset(['1->0'])
            
        if is_winning(state):
            return []
        if max_depth == 0:
            return None
            
        state_key = (state, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
            
        # Candidates for query:
        candidates = ['0', '0->1', '1->0', '0=1', '¬(1->0)', '¬(0->1)', '¬(0=1)']
        for q in candidates:
            if q in matched_so_far:
                continue
                
            # Define what we gain in both branches:
            if q == '0':
                s1 = state | frozenset(['0'])
                s2 = state | frozenset(['¬0'])
            elif q == '0->1':
                s1 = state | frozenset(['0->1'])
                s2 = state | frozenset(['¬(0->1)'])
            elif q == '1->0':
                s1 = state | frozenset(['1->0'])
                s2 = state | frozenset(['¬(1->0)'])
            elif q == '0=1':
                s1 = state | frozenset(['0=1'])
                s2 = state | frozenset(['¬(0=1)'])
            elif q == '¬(1->0)':
                s1 = state | frozenset(['¬(1->0)'])
                s2 = state | frozenset(['¬¬(1->0)'])
            else:
                continue
                
            if s1 == state and s2 == state:
                continue
                
            r1 = solve(s1, max_depth - 1, matched_so_far | {q})
            if r1 is not None:
                r2 = solve(s2, max_depth - 1, matched_so_far | {q})
                if r2 is not None:
                    memo[state_key] = (q, r1, r2)
                    return (q, r1, r2)
                    
        memo[state_key] = None
        return None

    for d in range(1, 10):
        print(f"Trying depth {d}...")
        res = solve(frozenset(), d, set())
        if res is not None:
            print(f"Found tree at depth {d}!")
            print_tree(res)
            break
    else:
        print("No tree found.")

def print_tree(node, indent=0):
    if not node:
        print(" " * indent + "WIN")
        return
    q, left, right = node
    print(" " * indent + f"Query {q}:")
    print(" " * indent + f"  Val branch (gains {q}):")
    print_tree(left, indent + 4)
    print(" " * indent + f"  Not_val branch:")
    print_tree(right, indent + 4)

find_proof_tree()
