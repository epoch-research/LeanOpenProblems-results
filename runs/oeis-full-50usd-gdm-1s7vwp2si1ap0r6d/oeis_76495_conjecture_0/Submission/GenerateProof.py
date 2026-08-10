import sympy

# Let's generate a list of lemmas that use decide for intervals.
# To check up to 2000, we can write a python script that outputs Lean code for Spec.lean.
# Wait, can we check up to some huge limit? No, 2000 is enough if we have a proof for x >= 2000, but actually, is there a simpler proof for x >= 24?
# Wait! Let's think: what if we can show that for x >= 24, there are no solutions by checking if we can just define a few intervals and use decide on them?
# Yes! We can write 40 lemmas of size 50!
# Let's write a python script to generate all 40 lemmas and compile Spec.lean to see if it works!
