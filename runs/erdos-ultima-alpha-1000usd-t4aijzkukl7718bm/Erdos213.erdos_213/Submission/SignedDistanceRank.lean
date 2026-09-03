import FormalConjecturesUtil

/-! Exact diagnostics for a restricted alternating-form construction.
This is not an obstruction to arbitrary rational-distance configurations. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Erdos213.SignedDistanceRank

/-- The six-by-six Pfaffian, in lexicographic upper-triangle coordinates. -/
def pf6 {R : Type*} [CommRing R] (a : Fin 15 → R) : R :=
  a 0*(a 9*a 14-a 10*a 13+a 11*a 12) -
  a 1*(a 6*a 14-a 7*a 13+a 8*a 12) +
  a 2*(a 5*a 14-a 7*a 11+a 8*a 10) -
  a 3*(a 5*a 13-a 6*a 11+a 8*a 9) +
  a 4*(a 5*a 12-a 6*a 10+a 7*a 9)

def alt {R : Type*} [CommRing R] (u v w t : Fin 6 → R) (i j : Fin 6) : R :=
  u i*v j-v i*u j+w i*t j-t i*w j

def upper {R : Type*} [CommRing R] (u v w t : Fin 6 → R) : Fin 15 → R :=
  ![alt u v w t 0 1,alt u v w t 0 2,alt u v w t 0 3,
    alt u v w t 0 4,alt u v w t 0 5,alt u v w t 1 2,
    alt u v w t 1 3,alt u v w t 1 4,alt u v w t 1 5,
    alt u v w t 2 3,alt u v w t 2 4,alt u v w t 2 5,
    alt u v w t 3 4,alt u v w t 3 5,alt u v w t 4 5]

lemma pf6_alt_zero {R : Type*} [CommRing R] (u v w t : Fin 6 → R) :
    pf6 (upper u v w t) = 0 := by
  dsimp [pf6,upper,alt]
  ring

def sign (b : Bool) : ℤ := if b then 1 else -1

/-- The first six known points, after removing their common distance scale.
Switching row/column signs normalizes the first five edges to be positive. -/
def knownSix (s : Fin 10 → Bool) : Fin 15 → ℤ :=
  ![22270,8636,16637,9248,22098,
    sign (s 0)*13746,sign (s 1)*11397,sign (s 2)*15138,sign (s 3)*21488,
    sign (s 4)*11049,sign (s 5)*5916,sign (s 6)*20066,
    sign (s 7)*7395,sign (s 8)*10795,sign (s 9)*14450]

lemma knownSix_pf6_ne : ∀ s : Fin 10 → Bool, pf6 (knownSix s) ≠ 0 := by
  decide

lemma knownSix_no_four_coordinate_representation (s : Fin 10 → Bool) :
    ¬∃ u v w t : Fin 6 → ℚ, upper u v w t = fun i => (knownSix s i : ℚ) := by
  rintro ⟨u,v,w,t,h⟩
  have hz := pf6_alt_zero u v w t
  rw [h] at hz
  apply knownSix_pf6_ne s
  have he : ((pf6 (knownSix s) : ℤ) : ℚ) = 0 := by
    simpa only [pf6,Int.cast_add,Int.cast_sub,Int.cast_mul] using hz
  exact_mod_cast he

#print axioms pf6_alt_zero
#print axioms knownSix_pf6_ne
#print axioms knownSix_no_four_coordinate_representation

end Erdos213.SignedDistanceRank
