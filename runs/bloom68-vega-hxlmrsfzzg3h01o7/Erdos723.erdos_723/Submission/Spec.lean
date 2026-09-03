import FormalConjecturesUtil

/-!
# Erdős Problem 723: The prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

open Configuration

namespace Erdos723

/--
If there is a finite projective plane of order $n$ then must $n$ be a prime power?
-/
theorem erdos_723 :
    ∀ {P L : Type} (_: Membership P L) (_ : Fintype P) (_ : Fintype L),
      ∀ pp : ProjectivePlane P L, IsPrimePow pp.order := by
  sorry

end Erdos723

theorem Erdos723.erdos_723.disproof : ¬ (type_of% @Erdos723.erdos_723) := sorry
