def solve():
    limit = 100000
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
        
    def get_sign(x):
        if x > 0: return 1
        if x < 0: return -1
        return 0
        
    import scipy.optimize as opt
    import numpy as np
    
    # Let's try different history sizes H
    for H in [1, 2, 3]:
        states = set()
        transitions = set()
        
        for n in range(H, limit):
            h_prev = (tuple(get_sign(a[n-1-i]) for i in range(H)), (n-1) % 6)
            h_next = (tuple(get_sign(a[n-i]) for i in range(H)), n % 6)
            s_next = get_sign(a[n])
            states.add(h_prev)
            states.add(h_next)
            transitions.add((h_prev, h_next, s_next))
            
        state_list = list(states)
        state_to_idx = {s: i for i, s in enumerate(state_list)}
        
        c = np.ones(len(state_list))
        A_ub = []
        b_ub = []
        
        for s_prev, s_next, val_next in transitions:
            row = np.zeros(len(state_list))
            row[state_to_idx[s_next]] += 1
            row[state_to_idx[s_prev]] -= 1
            A_ub.append(row)
            b_ub.append(-val_next)
            
        res = opt.linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=(0, 100))
        if res.success:
            print(f"H={H} with mod 6: Success!")
            # Print some values
            # for s, val in zip(state_list, res.x):
            #     print(f"  V({s}) = {val:.4f}")
        else:
            print(f"H={H} with mod 6: Failed.")

solve()
