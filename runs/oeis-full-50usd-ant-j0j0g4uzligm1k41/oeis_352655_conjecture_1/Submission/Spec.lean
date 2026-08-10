import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352655: $a(n) = \frac{1}{2} (\text{A005258}(n) + \text{A005258}(n-1)),$
where A005258$(n)$ is the central Apéry number $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}.$
-/
def a (n : ℕ) : ℕ :=
  let apery_A005258 (i : ℕ) : ℕ :=
    Finset.sum (range (i + 1)) (fun k => (i.choose k) ^ 2 * ((i + k).choose k))
  if n = 0 then 0
  else
    (apery_A005258 n + apery_A005258 (n - 1)) / 2

/-- Key binomial identity: `C(n,k)·C(n+k,k) = C(n+k,2k)·C(2k,k)`. -/
theorem choose_mul_add_choose (n k : ℕ) :
    n.choose k * (n + k).choose k = (n + k).choose (2 * k) * (2 * k).choose k := by
  by_cases hkn : k ≤ n
  · have hF : 0 < k ! * k ! * (n - k)! := by positivity
    have e1 : n.choose k * (n + k).choose k * (k ! * k ! * (n - k)!) = (n + k)! := by
      have hA : n.choose k * k ! * (n - k)! = n ! :=
        Nat.choose_mul_factorial_mul_factorial hkn
      have hB : (n + k).choose k * k ! * n ! = (n + k)! := by
        have := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
        rwa [show (n + k) - k = n by omega] at this
      calc n.choose k * (n + k).choose k * (k ! * k ! * (n - k)!)
          = (n.choose k * k ! * (n - k)!) * ((n + k).choose k * k !) := by ring
        _ = n ! * ((n + k).choose k * k !) := by rw [hA]
        _ = (n + k).choose k * k ! * n ! := by ring
        _ = (n + k)! := hB
    have e2 : (n + k).choose (2 * k) * (2 * k).choose k * (k ! * k ! * (n - k)!) = (n + k)! := by
      have hC : (n + k).choose (2 * k) * (2 * k)! * (n - k)! = (n + k)! := by
        have := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ n + k by omega)
        rwa [show (n + k) - 2 * k = n - k by omega] at this
      have hD : (2 * k).choose k * k ! * k ! = (2 * k)! := by
        have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
        rwa [show 2 * k - k = k by omega] at this
      calc (n + k).choose (2 * k) * (2 * k).choose k * (k ! * k ! * (n - k)!)
          = (n + k).choose (2 * k) * ((2 * k).choose k * k ! * k !) * (n - k)! := by ring
        _ = (n + k).choose (2 * k) * (2 * k)! * (n - k)! := by rw [hD]
        _ = (n + k)! := hC
    exact Nat.eq_of_mul_eq_mul_right hF (e1.trans e2.symm)
  · push_neg at hkn
    rw [Nat.choose_eq_zero_of_lt hkn, Nat.zero_mul,
        Nat.choose_eq_zero_of_lt (by omega : n + k < 2 * k), Nat.zero_mul]

/-- The central binomial coefficient `C(2k,k)` is even for `k ≥ 1`. -/
theorem two_dvd_centralBinom {k : ℕ} (hk : 1 ≤ k) : 2 ∣ (2 * k).choose k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h2k : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [h2k, Nat.choose_succ_succ (2 * m + 1) m]
  have hsymm : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
    rw [← Nat.choose_symm (show m ≤ 2 * m + 1 by omega)]
    congr 1
    omega
  rw [hsymm]
  exact ⟨(2 * m + 1).choose (m + 1), by ring⟩

/-- For `k ≥ 1`, `2 ∣ C(n,k)·C(n+k,k)`. -/
theorem two_dvd_choose_mul {n k : ℕ} (hk : 1 ≤ k) : 2 ∣ n.choose k * (n + k).choose k := by
  rw [choose_mul_add_choose]
  exact Dvd.dvd.mul_left (two_dvd_centralBinom hk) _

/-- For `k ≥ 1`, each Apéry summand `C(n,k)²·C(n+k,k)` is even. -/
theorem two_dvd_term {n k : ℕ} (hk : 1 ≤ k) : 2 ∣ (n.choose k) ^ 2 * (n + k).choose k := by
  have h : (n.choose k) ^ 2 * (n + k).choose k = n.choose k * (n.choose k * (n + k).choose k) := by
    ring
  rw [h]
  exact Dvd.dvd.mul_left (two_dvd_choose_mul hk) _

/-- The (numerator) Apéry number `A005258(i) = ∑ C(i,k)²·C(i+k,k)`. -/
def Bnum (i : ℕ) : ℕ := Finset.sum (range (i + 1)) (fun k => (i.choose k) ^ 2 * ((i + k).choose k))

/-- The ζ(2)-Apéry numbers `A005258` are always odd. -/
theorem Bnum_odd (n : ℕ) : Bnum n % 2 = 1 := by
  unfold Bnum
  rw [Finset.sum_range_succ']
  have hf0 : (n.choose 0) ^ 2 * ((n + 0).choose 0) = 1 := by simp
  have heven : 2 ∣ ∑ k ∈ range n, (n.choose (k + 1)) ^ 2 * ((n + (k + 1)).choose (k + 1)) := by
    apply Finset.dvd_sum
    intro i _
    exact two_dvd_term (by omega)
  obtain ⟨c, hc⟩ := heven
  rw [hf0, hc]
  omega

/-- `a n` equals `(Bnum n + Bnum (n-1))/2` for `n ≥ 1`. -/
theorem a_eq (n : ℕ) (hn : n ≠ 0) : a n = (Bnum n + Bnum (n - 1)) / 2 := by
  simp only [a, hn, if_false]
  rfl

/-- For `n ≥ 1`, `2 * a n = Bnum n + Bnum (n-1)` (the sum of two odd numbers is even). -/
theorem two_mul_a (n : ℕ) (hn : n ≠ 0) : 2 * a n = Bnum n + Bnum (n - 1) := by
  rw [a_eq n hn]
  have h1 := Bnum_odd n
  have h2 := Bnum_odd (n - 1)
  omega

/-- **Crux supercongruence** (the deep Apéry-type content of the conjecture):
`p^{3r+3}` divides `(B(p^r)+B(p^r-1)) - (B(p^{r-1})+B(p^{r-1}-1))`. -/
theorem crux {p r : ℕ} (hp : Nat.Prime p) (hp5 : p ≥ 5) (hr : r ≥ 2) :
    Nat.ModEq (p ^ (3 * r + 3))
      (Bnum (p ^ r) + Bnum (p ^ r - 1)) (Bnum (p ^ (r - 1)) + Bnum (p ^ (r - 1) - 1)) := by
  sorry

/--
Conjecture: for r ≥ 2, and all primes p ≥ 5, a(p^r) ≡ a(p^(r-1)) ( mod p^(3*r+3) ). - Peter Bala
-/
theorem oeis_352655_conjecture_1 :
  ∀ (p r : ℕ),
    Nat.Prime p →
    p ≥ 5 →
    r ≥ 2 →
    Nat.ModEq (p ^ (3 * r + 3)) (a (p ^ r)) (a (p ^ (r - 1))) := by
  intro p r hp hp5 hr
  have hp0 : p ≠ 0 := by omega
  have hpr : (p : ℕ) ^ r ≠ 0 := pow_ne_zero _ hp0
  have hpr1 : (p : ℕ) ^ (r - 1) ≠ 0 := pow_ne_zero _ hp0
  have hodd : Odd (p ^ (3 * r + 3)) := by
    apply Odd.pow
    rcases hp.eq_two_or_odd' with h2 | hodd
    · omega
    · exact hodd
  have hcop : Nat.gcd (p ^ (3 * r + 3)) 2 = 1 := Nat.coprime_two_right.mpr hodd
  have h2 : Nat.ModEq (p ^ (3 * r + 3)) (2 * a (p ^ r)) (2 * a (p ^ (r - 1))) := by
    rw [two_mul_a _ hpr, two_mul_a _ hpr1]
    exact crux hp hp5 hr
  exact Nat.ModEq.cancel_left_of_coprime hcop h2
