def solve():
    limit = 10000000 # 10 million
    
    # We can't run python for 10 million easily because it might be slow.
    # But let's run up to 100,000 first, where we know they match.
    # Let's compare up to 10 million using a fast python loop.
    
    # In python:
    a_prev2 = 0
    a_prev1 = 1
    for b in range(2, limit):
        val = (a_prev1 ^ b) - a_prev2
        a_prev2 = a_prev1
        a_prev1 = val
        
    print(f"Python at {limit-1}: {a_prev1}")

solve()
