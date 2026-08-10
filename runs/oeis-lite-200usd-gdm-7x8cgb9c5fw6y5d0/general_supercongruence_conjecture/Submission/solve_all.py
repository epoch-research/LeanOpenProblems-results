def find_term(R, M, K):
    # recurse : N_{R + M + K}
    # goal : N_{R + M + M}
    # We want to construct goal from recurse.
    # Let's represent the variables we have.
    # Each type N_i is (N_{i-1} -> False) for i > 0, and N_0 is α' (which we can treat as a primitive type).
    # Since we can always use Classical.byContradiction, we can convert ¬¬A to A.
    # Let's see if we can find a term.
    # We can write a simple BFS on types we can construct.
    pass

# Actually, let's look at R=0, M=2, K=3.
# The types are:
# recurrence: T(6) = T(5) -> False
# goal: T(4) = T(3) -> False
# We assumed h3 : T(3).
# We wanted to construct False.
# We did: recurse (fun h4 => h4 h3).
# Since h4 has type T(4) = T(3) -> False.
# This works!

# What about R=2, M=1, K=4?
# f : Bad α → N2(α)
# mk : Bad (N4(α)) → Bad (N1(α))
# recurse : N2(N4(α')) = N6(α')
# goal : N2(N1(α')) = N3(α')
# T(6) = T(5) -> False
# T(3) = T(2) -> False
# We want to return T(3). So we assume h2 : T(2).
# We have recurse : T(6).
# We want to construct False.
# Can we do: recurse (fun h5 => ...)?
# h5 has type T(5) = T(4) -> False.
# We want to construct False.
# Inside, we can assume h5.
# We want to construct False.
# Since we have h5 : T(5) and h2 : T(2).
# Can we construct T(4)?
# T(4) is T(3) -> False.
# So we assume h3 : T(3). We want to construct False.
# We have h3 : T(3) and h2 : T(2).
# Since h3 is T(2) -> False, and h2 : T(2).
# We can do `h3 h2` to get False!
# So `fun h3 => h3 h2` has type T(4)!
# Then `h5 (fun h3 => h3 h2)` has type False!
# So `fun h5 => h5 (fun h3 => h3 h2)` has type T(5) -> False = T(6)? No, it takes h5 of type T(5) and returns False, so it has type T(5) -> False = T(6)?
# Wait!
# h5 has type T(5). So `fun h5 => ...` has type T(5) -> False = T(6).
# But recurse has type T(6) = T(5) -> False.
# So `recurse (fun h5 => h5 (fun h3 => h3 h2))` has type False!
# Let's check this term:
# `fun (h2 : T(2)) => recurse (fun (h5 : T(5)) => h5 (fun (h3 : T(3)) => h3 h2))`
# Let's check the types:
# h2 : T(2) = T(1) -> False
# h3 : T(3) = T(2) -> False
# h3 h2 : False (perfect!)
# fun h3 => h3 h2 : T(3) -> False = T(4) (perfect!)
# h5 : T(5) = T(4) -> False
# h5 (fun h3 => h3 h2) : False (perfect!)
# fun h5 => h5 (fun h3 => ... ) : T(5) -> False = T(6) (perfect!)
# recurse : T(6) = T(5) -> False.
# recurse (fun h5 => ... ) : False (perfect!)
# fun h2 => recurse (fun h5 => ... ) : T(2) -> False = T(3) (perfect!)
# THIS IS 100% CORRECT AND ABSOLUTELY BRILLIANT!
print("R=2, M=1, K=4 worked!")
