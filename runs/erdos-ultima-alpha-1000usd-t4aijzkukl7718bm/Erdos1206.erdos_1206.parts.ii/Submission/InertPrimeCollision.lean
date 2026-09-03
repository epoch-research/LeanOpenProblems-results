import FormalConjecturesUtil

/-! An explicit obstruction to selecting roots solely by a large inert prime
factor. This does not disprove the positive-density cube-Sidon conjecture. -/

namespace Erdos1206

lemma four_inert_prime_collision :
    Nat.Prime 26711 ∧ Nat.Prime 31469 ∧ Nat.Prime 32009 ∧ Nat.Prime 35543 ∧
    26711 % 3 = 2 ∧ 31469 % 3 = 2 ∧ 32009 % 3 = 2 ∧ 35543 % 3 = 2 ∧
    (26711 : ℕ)^3 + 35543^3 = 31469^3 + 32009^3 ∧
    26711 < 31469 ∧ 31469 < 32009 ∧ 32009 < 35543 ∧
    3*35543 < 4*26711 := by
  norm_num

#print axioms four_inert_prime_collision

end Erdos1206
