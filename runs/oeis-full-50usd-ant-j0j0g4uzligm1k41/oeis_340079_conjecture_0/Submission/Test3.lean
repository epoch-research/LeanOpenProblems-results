import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def S (n : ℕ) : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n

theorem S_eq_range (n : ℕ) (hn : 1 ≤ n) :
    S n = ∑ k ∈ Finset.range n, Nat.gcd n k := by
  unfold S
  rw [Finset.sum_Ico_succ_top hn]
  have e2 : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [e2, Finset.sum_insert (by simp)]
  rw [Nat.gcd_self, Nat.gcd_zero_right]
  have hc : (Finset.Ico 1 n).sum (fun k => Nat.gcd k n)
      = (Finset.Ico 1 n).sum (fun k => Nat.gcd n k) :=
    Finset.sum_congr rfl (fun k _ => Nat.gcd_comm k n)
  rw [hc]; ring

theorem S_eq_sum_div (n : ℕ) (hn : 1 ≤ n) :
    S n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  rw [S_eq_range n hn]
  rw [← Finset.sum_fiberwise_of_maps_to (t := n.divisors) (g := fun k => Nat.gcd n k)
        (f := fun k => Nat.gcd n k)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hall : ∀ k ∈ (Finset.range n).filter (fun k => Nat.gcd n k = d),
        Nat.gcd n k = d := fun k hk => (Finset.mem_filter.1 hk).2
    rw [Finset.sum_congr rfl hall, Finset.sum_const, ← Nat.totient_div_of_dvd hdvd,
        smul_eq_mul, mul_comm]
  · intro k _
    rw [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left n k, by omega⟩

theorem p_dvd_totient_of_sq {p m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0) (h : p ^ 2 ∣ m) :
    p ∣ Nat.totient m := by
  set a := m.factorization p with ha
  have ha2 : 2 ≤ a := by
    rw [ha]; exact (Nat.Prime.pow_dvd_iff_le_factorization hp hm0).1 h
  have hsplit : p ^ a * (ordCompl[p] m) = m := by
    have h2 := Nat.ordProj_mul_ordCompl_eq_self m p
    simpa [ha] using h2
  have hcop : Nat.Coprime (p ^ a) (ordCompl[p] m) := (Nat.coprime_ordCompl hp hm0).pow_left a
  rw [← hsplit, Nat.totient_mul hcop]
  have hpt : p ∣ Nat.totient (p ^ a) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega : a - 1 ≠ 0)) _
  exact Dvd.dvd.mul_right hpt _

theorem nonsquarefree_dvd_S {p n : ℕ} (hp : p.Prime) (hpp : p ^ 2 ∣ n) : p ∣ S n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [S]
  · rw [S_eq_sum_div n hn]
    apply Finset.dvd_sum
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    by_cases hpd : p ∣ d
    · exact Dvd.dvd.mul_right hpd _
    · have hnd0 : n / d ≠ 0 := by
        have := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd_pos; omega
      have hcop : Nat.Coprime (p ^ 2) d := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).pow_left 2
      obtain ⟨c, hc⟩ := hdvd
      have hnd : n / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd_pos
      have hsq : p ^ 2 ∣ (n / d) := by
        rw [hnd]; rw [hc] at hpp
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop hpp
      exact Dvd.dvd.mul_left (p_dvd_totient_of_sq hp hnd0 hsq) d
