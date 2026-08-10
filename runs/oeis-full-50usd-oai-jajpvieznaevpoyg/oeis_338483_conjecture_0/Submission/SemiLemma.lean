import FormalConjectures.Util.ProblemImports
open Finset Nat Set

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

lemma tau_mul_prime_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    tau (p * q) = 4 := by
  unfold tau
  rw [Nat.card_divisors (mul_ne_zero hp.ne_zero hq.ne_zero)]
  have hpf : (p * q).primeFactors = ({p, q} : Finset ℕ) := by
    ext r
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hrp, hdvd, _⟩
      rcases hrp.dvd_or_dvd hdvd with h | h
      · left
        exact ((hp.dvd_iff_eq hrp.ne_one).mp h).symm
      · right
        exact ((hq.dvd_iff_eq hrp.ne_one).mp h).symm
    · intro h
      rcases h with hr | hr
      · subst r
        exact ⟨hp, dvd_mul_right p q, mul_ne_zero hp.ne_zero hq.ne_zero⟩
      · subst r
        exact ⟨hq, dvd_mul_left q p, mul_ne_zero hp.ne_zero hq.ne_zero⟩

  rw [hpf]
  have hpq' : q ≠ p := hpq.symm
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  have hqp0 : q.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hpq ((hq.dvd_iff_eq hp.ne_one).mp hd).symm
  have hpq0 : p.factorization q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hpq ((hp.dvd_iff_eq hq.ne_one).mp hd)
  simp [Finset.prod_insert, hpq, hpq', hp.factorization_self,
    hq.factorization_self, hqp0, hpq0]
