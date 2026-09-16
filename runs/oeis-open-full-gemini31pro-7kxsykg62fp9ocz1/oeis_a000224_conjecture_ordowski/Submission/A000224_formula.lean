import Mathlib
import Submission.Spec
open Finset

-- If n = a * b with a, b >= 3 odd and coprime:
-- A(n) = A(a) * A(b).
-- Since a is odd, A(a) <= (a+1)/2. Since b is odd, A(b) <= (b+1)/2.
-- Thus A(n) <= (a+1)(b+1)/4.
-- M = A(n)(A(n)-1) <= ((a+1)(b+1)/4) * (((a+1)(b+1)/4) - 1).
