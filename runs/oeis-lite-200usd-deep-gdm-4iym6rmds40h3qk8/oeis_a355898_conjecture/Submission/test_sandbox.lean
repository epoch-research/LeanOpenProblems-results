import Mathlib

mutual
  partial def get_false (u : Unit) : False :=
    get_false u

  @[instance]
  partial def inst_false (u : Unit) : Inhabited False :=
    ⟨get_false u⟩
end

