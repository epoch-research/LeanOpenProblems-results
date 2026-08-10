import itertools

def solve():
    # We have a set of variables:
    #   p0: P (0 or 1)
    #   d0: safe_dec P (0 for isFalse, 1 for isTrue)
    #   d_not: safe_dec (¬P) (0 for isFalse, 1 for isTrue)
    #   d_ex: safe_dec (∃ h: ¬P, safe_dec P = isFalse h) (0 or 1)
    #   d_ex_not: safe_dec (∃ h: ¬P, safe_dec (¬P) = isTrue h) (0 or 1)
    #   d_ex_not_not: safe_dec (∃ h: ¬¬P, safe_dec (¬¬P) = isTrue h) (0 or 1)
    #   d_ex_not_not_not: safe_dec (∃ h: ¬¬P → False, safe_dec (¬¬P) = isFalse h) (0 or 1)
    #   d_not_not: safe_dec (¬¬P) (0 or 1)
    #   d_not_not_not: safe_dec (¬¬¬P) (0 or 1)
    #   d_ex_4: safe_dec (∃ h: ¬¬¬P, safe_dec (¬¬¬P) = isTrue h) (0 or 1)
    #   d_ex_5: safe_dec (∃ h: ¬¬¬P → False, safe_dec (¬¬¬P) = isFalse h) (0 or 1)
    #   d_ex_6: safe_dec (∃ h: ¬¬¬P, safe_dec (¬¬P) = isFalse h) (0 or 1)
    #   d_not_not_not_not: safe_dec (¬¬¬¬P) (0 or 1)
    
    # Let's list the constraints we can enforce in Lean:
    open_branches = []
    for (d0, d_not, d_ex, d_ex_not, d_ex_not_not, d_ex_not_not_not, 
         d_not_not, d_not_not_not, d_ex_4, d_ex_5, d_ex_6, d_not_not_not_not) in itertools.product([0, 1], repeat=12):
         
        # 1. d0 == 1 ==> closed
        if d0 == 1: continue
        # 3. d0 == 0 and d_not == 0 ==> closed
        if d0 == 0 and d_not == 0: continue
        # 4. d0 == 0 and d_ex == 0 ==> closed
        if d0 == 0 and d_ex == 0: continue
        # 6. d_not == 1 and d_ex_not == 0 ==> closed
        if d_not == 1 and d_ex_not == 0: continue
        # 7. d_ex_not_not == 1 and d0 == 0 ==> closed
        if d_ex_not_not == 1 and d0 == 0: continue
        # 8. d_ex_not_not == 0 and d_ex_not_not_not == 0 ==> closed
        if d_ex_not_not == 0 and d_ex_not_not_not == 0: continue
        # 9. d_ex_not_not_not == 1 and d_not_not == 1 ==> closed
        if d_ex_not_not_not == 1 and d_not_not == 1: continue
        # 10. d_not_not == 1 and d0 == 0 ==> closed
        if d_not_not == 1 and d0 == 0: continue
        
        # New level:
        # If d_not_not_not == 0, we get ¬¬¬¬P.
        # But from d_not_not == 0, we have ¬¬¬P.
        # So we have ¬¬¬P and ¬¬¬¬P ==> closed!
        if d_not_not == 0 and d_not_not_not == 0: continue
        
        # Since d_not_not_not == 1, we can prove Q_ex_4 := (∃ h: ¬¬¬P, safe_dec (¬¬¬P) = isTrue h)
        # So if d_ex_4 == 0 ==> closed!
        if d_not_not_not == 1 and d_ex_4 == 0: continue
        
        # Q_ex_5 := (∃ h: ¬¬¬P → False, safe_dec (¬¬¬P) = isFalse h)
        # We can prove Q_ex_4 ∨ Q_ex_5.
        # So if d_ex_4 == 0 and d_ex_5 == 0 ==> closed!
        if d_ex_4 == 0 and d_ex_5 == 0: continue
        
        # If d_ex_5 == 1, we get eq: safe_dec (¬¬¬P) = isFalse h.
        # If d_not_not_not == 1, safe_dec (¬¬¬P) is isTrue h ==> closed!
        if d_ex_5 == 1 and d_not_not_not == 1: continue
        
        # If d_not_not == 0, we get h: ¬¬¬P and safe_dec (¬¬P) = isFalse h.
        # So we can prove Q_ex_6 := (∃ h: ¬¬¬P, safe_dec (¬¬P) = isFalse h).
        # So if d_ex_6 == 0 ==> closed!
        if d_not_not == 0 and d_ex_6 == 0: continue
        
        # If d_ex_6 == 1, we get eq: safe_dec (¬¬P) = isFalse h.
        # If d_not_not == 1, safe_dec (¬¬P) is isTrue h ==> closed!
        if d_ex_6 == 1 and d_not_not == 1: continue
        
        # NEW CONSTRAINT:
        # If d_not_not == 0, we have h: ¬¬¬P.
        # If d_not_not_not_not == 1, we have h2: ¬¬¬¬P (which is ¬¬¬P → False).
        # So we get False!
        if d_not_not == 0 and d_not_not_not_not == 1: continue
        
        open_branches.append((d0, d_not, d_ex, d_ex_not, d_ex_not_not, d_ex_not_not_not, 
                              d_not_not, d_not_not_not, d_ex_4, d_ex_5, d_ex_6, d_not_not_not_not))
                              
    print(f"Number of open branches: {len(open_branches)}")
    for b in open_branches:
        print(f"  Branch: {b}")

solve()
