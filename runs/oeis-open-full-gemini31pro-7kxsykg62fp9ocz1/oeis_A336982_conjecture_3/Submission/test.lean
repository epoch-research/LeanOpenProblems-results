import Submission.Spec
open Nat Finset ZMod

#eval S_sum 13 % 169
#eval (legendreSym 13 (-1 : ℤ)) * (2 * 13 - 12 * 1) % 169
