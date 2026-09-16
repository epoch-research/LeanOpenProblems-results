import Mathlib
import Submission.Spec
open Finset

-- Wait, what if the conjecture is FALSE?
-- Did I search high enough? I searched p, q up to 100,000 for n=p*q, and found NO counterexamples.
-- What if n is not squarefree? A(p^2) = (p^2 - p)/2 + A(1) = (p^2 - p + 2)/2.
-- So A(9) = (9-3+2)/2 = 4. 4*3 = 12. 9^2-1 = 80. 12 doesn't divide 80.
-- What about A(25)? A(25) = (25-5+2)/2 = 11. 11*10 = 110. 25^2-1 = 624. 110 doesn't divide 624.
-- What about A(27)? A(p^3) = (p^3 - p^2)/2 + A(p) = (p^3 - p^2 + p + 1)/2.
-- A(27) = (27-9+3+1)/2 = 11. 11*10 = 110. 27^2-1 = 728.
-- So prime powers don't work.

-- Let's consider `A000224` definition. A(n) = card { x^2 mod n }.
-- So actually my A(p^k) formula is correct. 
-- And I also tested composite numbers up to 10^7 with python/C++.
-- So the ONLY IF direction is TRUE. We need to formally PROVE it.
