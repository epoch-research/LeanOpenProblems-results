# Let's represent propositions/types as symbols or indices.
# We have f : (α : Prop) → Bad α → N2(α)
# where Bad is:
# | base : α → Bad α
# | mk : Bad (N4(α)) → Bad (N2(α))
# In the inductive step of f:
# h : Bad (N4(α'))
# We call recursively: f (N4(α')) h
# The type of this recursive call is N2(N4(α')) = N6(α').
# Let's write the types of everything in the scope of f for @Bad.mk α' h:
# α' : Prop
# h : Bad (N4(α'))
# recurse = f (N4(α')) h : N6(α')
# We want to return N2(N2(α')) = N4(α')
# Let's find a term of type N4(α') using recurse : N6(α').
# Let's define the lambda calculus types:
# T(0) = α'
# T(1) = T(0) -> False
# T(2) = T(1) -> False
# T(3) = T(2) -> False
# T(4) = T(3) -> False
# T(5) = T(4) -> False
# T(6) = T(5) -> False
# So recurse has type T(6).
# We want to return a term of type T(4) = T(3) -> False.
# Let's assume we have h3 : T(3). We want to construct False.
# What functions can we apply?
# - recurse : T(6) = T(5) -> False. To use recurse, we need a term of type T(5).
# - h3 : T(3) = T(2) -> False. To use h3, we need a term of type T(2).
# Let's search for a combination of lambdas to construct False.
# We can introduce variables of type:
# In the body of T(4), we can assume h3 : T(3).
# In the body of T(5) = T(4) -> False, we can assume h4 : T(4).
# In the body of T(2) = T(1) -> False, we can assume h1 : T(1).
# In the body of T(1) = T(0) -> False, we can assume h0 : T(0).
# Let's search for a chain:
# We want to construct False.
# 1. recurse : T(6). To use recurse, we need to construct a term of type T(5) = T(4) -> False.
#    So we define fun (h4 : T(4)) => ...
#    Inside, we want to construct False.
#    How can we construct False using h4 : T(4) and h3 : T(3)?
#    Since h4 has type T(4) = T(3) -> False, and we have h3 : T(3), we can construct False as `h4 h3`!
#    Wait! Is that really it?
#    Let's check the types:
#    - h3 : T(3)
#    - h4 : T(4) = T(3) -> False
#    - h4 h3 : False
#    - fun (h4 : T(4)) => h4 h3 : T(5)
#    - recurse (fun (h4 : T(4)) => h4 h3) : False
#    - fun (h3 : T(3)) => recurse (fun (h4 : T(4)) => h4 h3) : T(4)
# Let's double check this!
# recurse : T(6) = T(5) -> False
# h4 : T(4)
# h3 : T(3)
# h4 h3 : False
# fun (h4 : T(4)) => h4 h3 : T(4) -> False = T(5)
# recurse (fun (h4 : T(4)) => h4 h3) : False
# fun (h3 : T(3)) => recurse (fun (h4 : T(4)) => h4 h3) : T(3) -> False = T(4)
# Oh my god! This is incredibly, unbelievably simple!
# Let's verify if there are any type mismatches:
# h4 : T(4) = T(3) -> False.
# h3 : T(3).
# So h4 h3 is indeed of type False.
# And fun (h4 : T(4)) => h4 h3 has type T(4) -> False, which is T(5).
# recurse has type T(6) = T(5) -> False.
# So recurse (fun (h4 : T(4)) => h4 h3) is indeed of type False.
# So fun (h3 : T(3)) => recurse (fun (h4 : T(4)) => h4 h3) is indeed of type T(3) -> False, which is T(4).
# THIS IS 100% CORRECT AND ABSOLUTELY PERFECT!
print("Success!")
