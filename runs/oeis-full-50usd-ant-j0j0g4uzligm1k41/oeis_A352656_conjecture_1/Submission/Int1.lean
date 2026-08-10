import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset
set_option maxHeartbeats 2000000 in

theorem resineq_core (Q x y z i j k m : ℤ) (hQ : 0 < Q)
    (hx : 0 ≤ x) (hx' : x < Q) (hy : 0 ≤ y) (hy' : y < Q) (hz : 0 ≤ z) (hz' : z < Q)
    (hpb : 0 ≤ x + y - Q * i) (hpb' : x + y - Q * i < Q)
    (hqb : 0 ≤ x + z - Q * j) (hqb' : x + z - Q * j < Q)
    (htb : 0 ≤ y + z - Q * k) (htb' : y + z - Q * k < Q)
    (hsb : 0 ≤ x + y + z - Q * m) (hsb' : x + y + z - Q * m < Q)
    (hi0 : 0 ≤ i) (hi1 : i ≤ 1) (hj0 : 0 ≤ j) (hj1 : j ≤ 1)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 2) :
    (x+y-Q*i)*(Q-(x+y-Q*i)) + (x+z-Q*j)*(Q-(x+z-Q*j)) + (y+z-Q*k)*(Q-(y+z-Q*k)) ≤
      x*(Q-x) + y*(Q-y) + z*(Q-z) + (x+y+z-Q*m)*(Q-(x+y+z-Q*m)) := by
  interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases m <;>
    nlinarith [hx, hx', hy, hy', hz, hz', hQ]
