import Submission.Spec
open Nat Int

def test_sum (n j k : ℕ) : Bool :=
  Id.run do
    for z in [-10:11] do
      for x in [0:10] do
        for y in [0:10] do
          let g := generalized_polygonal_num_of_sides 7 z
          let p1 := polygonal_num_of_sides j x
          let p2 := polygonal_num_of_sides k y
          if g + p1 + p2 == n then
            return true
    return false

def check_all_n (j k max_n : ℕ) : Bool :=
  Id.run do
    for n in [0:max_n] do
      if not (test_sum n j k) then
        return false
    return true

#eval check_all_n 3 3 50
#eval check_all_n 8 9 50
