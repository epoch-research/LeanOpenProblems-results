import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

/--
A265710 a(n) = 2 for n = 14, 244, 494, 45994. Are there any others? - Robert Israel, Apr 02 2017
-/
theorem oeis_A265710_conjecture :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  intro n _hn
  constructor
  · -- Forward direction: this is the open part of the conjecture (Robert Israel, 2017).
    intro h
    sorry
  · intro h
    have hm := (isMultiplicative_sigma (k := 1))
    rcases h with rfl | rfl | rfl | rfl
    · -- a 14 = 2
      have hd : Nat.divisors 14 = {1,2,7,14} := by decide
      unfold a; rw [hd]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [show sigma 1 1 = 1 from by decide, show sigma 1 2 = 3 from by decide,
          show sigma 1 7 = 8 from by decide, show sigma 1 14 = 24 from by decide]
      norm_num
    · -- a 244 = 2
      have hd : Nat.divisors 244 = {1,2,4,61,122,244} := by decide
      unfold a; rw [hd]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [show sigma 1 1 = 1 from by decide, show sigma 1 2 = 3 from by decide,
          show sigma 1 4 = 7 from by decide, show sigma 1 61 = 62 from by decide,
          show sigma 1 122 = 186 from by decide, show sigma 1 244 = 434 from by decide]
      norm_num
    · -- a 494 = 2
      have hd : Nat.divisors 494 = {1,2,13,19,26,38,247,494} := by decide
      unfold a; rw [hd]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [show sigma 1 1 = 1 from by decide, show sigma 1 2 = 3 from by decide,
          show sigma 1 13 = 14 from by decide, show sigma 1 19 = 20 from by decide,
          show sigma 1 26 = 42 from by decide, show sigma 1 38 = 60 from by decide,
          show sigma 1 247 = 280 from by decide, show sigma 1 494 = 840 from by decide]
      norm_num
    · -- a 45994 = 2
      have hd : Nat.divisors 45994 =
          {1,2,13,26,29,58,61,122,377,754,793,1586,1769,3538,22997,45994} := by
        rw [show (45994:ℕ) = 2*(13*(29*61)) from by norm_num,
            Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul]
        decide
      have e377 : sigma 1 377 = 420 := by
        have := hm.map_mul_of_coprime (m:=13) (n:=29) (by decide); simpa using this
      have e754 : sigma 1 754 = 1260 := by
        have := hm.map_mul_of_coprime (m:=2) (n:=377) (by decide)
        rw [show (2*377:ℕ)=754 from by norm_num, e377] at this; simpa using this
      have e793 : sigma 1 793 = 868 := by
        have := hm.map_mul_of_coprime (m:=13) (n:=61) (by decide); simpa using this
      have e1586 : sigma 1 1586 = 2604 := by
        have := hm.map_mul_of_coprime (m:=2) (n:=793) (by decide)
        rw [show (2*793:ℕ)=1586 from by norm_num, e793] at this; simpa using this
      have e1769 : sigma 1 1769 = 1860 := by
        have := hm.map_mul_of_coprime (m:=29) (n:=61) (by decide); simpa using this
      have e3538 : sigma 1 3538 = 5580 := by
        have := hm.map_mul_of_coprime (m:=2) (n:=1769) (by decide)
        rw [show (2*1769:ℕ)=3538 from by norm_num, e1769] at this; simpa using this
      have e22997 : sigma 1 22997 = 26040 := by
        have := hm.map_mul_of_coprime (m:=13) (n:=1769) (by decide)
        rw [show (13*1769:ℕ)=22997 from by norm_num, e1769] at this; simpa using this
      have e45994 : sigma 1 45994 = 78120 := by
        have := hm.map_mul_of_coprime (m:=2) (n:=22997) (by decide)
        rw [show (2*22997:ℕ)=45994 from by norm_num, e22997] at this; simpa using this
      unfold a; rw [hd]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [show sigma 1 1 = 1 from by decide, show sigma 1 2 = 3 from by decide,
          show sigma 1 13 = 14 from by decide, show sigma 1 26 = 42 from by decide,
          show sigma 1 29 = 30 from by decide, show sigma 1 58 = 90 from by decide,
          show sigma 1 61 = 62 from by decide, show sigma 1 122 = 186 from by decide,
          e377, e754, e793, e1586, e1769, e3538, e22997, e45994]
      norm_num
