import Submission.PolyId25
import Mathlib

open Nat

-- We have:
-- D(n, r) * 2^r * (4n).descFactorial r = (8n).descFactorial (2r)

-- And we know:
-- a(n) = (8n)! * n! / ( (4n)! * (3n)! * (2n)! )
-- (8n).descFactorial (2r) = (8n)! / (8n - 2r)!
-- (4n).descFactorial r = (4n)! / (4n - r)!

-- So D(n, r) * 2^r * (4n)! / (4n - r)! = (8n)! / (8n - 2r)!
-- Thus D(n, r) = (8n)! (4n - r)! / ( (8n - 2r)! (4n)! 2^r )

-- Then a(n) / D(n, r) = [ (8n)! n! / ((4n)! (3n)! (2n)!) ] * [ (8n-2r)! (4n)! 2^r / ( (8n)! (4n-r)! ) ]
-- a(n) / D(n, r) = (8n-2r)! n! 2^r / ( (4n-r)! (3n)! (2n)! )

-- So a(n) * (8r)! / D(n, r) = (8n-2r)! n! (8r)! 2^r / ( (4n-r)! (3n)! (2n)! ) = V(n, r) * 2^r
-- Where V(n, r) = (8n-2r)! n! (8r)! / ( (4n-r)! (3n)! (2n)! )

-- So if we can show V(n, r) is an integer, we are done!
