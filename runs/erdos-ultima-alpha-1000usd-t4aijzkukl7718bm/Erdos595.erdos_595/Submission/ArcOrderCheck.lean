import FormalConjecturesUtil
example {A : Type*} [LinearOrder A] (a b c : A) (hab : a < b) (hbc : b < c) (hca : c = a) : False := by
  order
