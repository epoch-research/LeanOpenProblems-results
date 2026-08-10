import FormalConjectures.Util.ProblemImports

open scoped BigOperators Nat Finset Int

/--
A352373: $a(n) = [x^n] \left( \frac{1}{(1 - x)^2(1 - x^2)} \right)^n$ for $n \ge 1$.
The sequence is explicitly given by the combinatorial sum:
$$a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} \binom{3n-2k-1}{n-2k} \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let n' := n
  Finset.sum (Finset.range (n' / 2 + 1)) fun k =>
    let term1_top := 3 * n' - 2 * k - 1
    let term1_bot := n' - 2 * k
    let term2_top := n' + k - 1
    let term2_bot := k
    (term1_top.choose term1_bot) * (term2_top.choose term2_bot)

open PowerSeries
namespace A352373
noncomputable section

def hp2 : (2:ℕ) ≠ 0 := by norm_num

lemma invOneSubPow_pow (d j : ℕ) : (invOneSubPow ℤ d) ^ j = invOneSubPow ℤ (d * j) := by
  rw [invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_eq_inv_one_sub_pow, ← pow_mul]

lemma coeff_invOneSubPow (d n : ℕ) (hd : 0 < d) :
    (PowerSeries.coeff n) (invOneSubPow ℤ d).val = ((Nat.choose (d - 1 + n) (d - 1) : ℕ) : ℤ) := by
  rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ d hd, coeff_mk]

/-- `Φ = 1/((1-X)^2(1-X^2))`. -/
def Φ : ℤ⟦X⟧ := (invOneSubPow ℤ 2).val * (expand 2 hp2 ((invOneSubPow ℤ 1).val))
/-- `D = (1-X)^2(1-X^2) = 1/Φ`. -/
def D : ℤ⟦X⟧ := (invOneSubPow ℤ 2).inv * (expand 2 hp2 ((invOneSubPow ℤ 1).inv))

lemma Phi_mul_D : Φ * D = 1 := by
  unfold Φ D
  rw [mul_mul_mul_comm, ← map_mul, (invOneSubPow ℤ 2).val_inv, (invOneSubPow ℤ 1).val_inv,
      map_one, mul_one]

lemma Phi_pow (j : ℕ) :
    Φ ^ j = (invOneSubPow ℤ (2*j)).val * (expand 2 hp2 ((invOneSubPow ℤ j).val)) := by
  unfold Φ
  rw [mul_pow]
  congr 1
  · rw [← Units.val_pow_eq_pow_val, invOneSubPow_pow]
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, invOneSubPow_pow, one_mul]

lemma coeff_mul_expand2 (P Q : ℤ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (P * expand 2 hp2 Q) =
      ∑ b ∈ Finset.range (n/2+1), (PowerSeries.coeff (n - 2*b) P) * (PowerSeries.coeff b Q) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_expand 2 hp2 Q, mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_nbij' (fun x => (n - x)/2) (fun b => n - 2*b)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx; simp only [Finset.mem_range]; omega
  · intro b hb; simp only [Finset.mem_range] at hb; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx; obtain ⟨_, m, hm⟩ := hx; omega
  · intro b hb; simp only [Finset.mem_range] at hb; omega
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx; obtain ⟨_, m, hm⟩ := hx
    have : n - 2 * ((n - x)/2) = x := by omega
    rw [this]

lemma coeff_expand_mul_left (p : ℕ) (hp : p ≠ 0) (R S : ℤ⟦X⟧) (M : ℕ) :
    PowerSeries.coeff M (expand p hp R * S) =
      ∑ t ∈ Finset.range (M/p+1), (PowerSeries.coeff t R) * (PowerSeries.coeff (M - p*t) S) := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_expand p hp R, ite_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  apply Finset.sum_nbij' (fun x => x/p) (fun t => p*t)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hx.1))
  · intro t ht; simp only [Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, Dvd.intro t rfl⟩
    have h1 : p * t ≤ p * (M/p) := by gcongr; exact Nat.lt_succ_iff.mp ht
    have h2 : p * (M/p) ≤ M := by rw [mul_comm]; exact Nat.div_mul_le_self M p
    exact Nat.lt_succ_of_le (le_trans h1 h2)
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx
    exact Nat.mul_div_cancel' hx.2
  · intro t _; exact Nat.mul_div_cancel_left t hp0
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_range] at hx
    rw [Nat.mul_div_cancel' hx.2]

/-- `g = Φ^p / Φ(X^p) = Φ^p · D(X^p)`. -/
def g (p : ℕ) (hp : p ≠ 0) : ℤ⟦X⟧ := Φ ^ p * expand p hp D

lemma expand_Phi_pow_mul_g_pow (p : ℕ) (hp : p ≠ 0) (J : ℕ) :
    expand p hp (Φ ^ J) * (g p hp) ^ J = Φ ^ (p * J) := by
  unfold g
  rw [mul_pow, ← map_pow, ← pow_mul, ← mul_assoc, mul_comm (expand p hp (Φ^J)) (Φ^(p*J)),
      mul_assoc, ← map_mul, ← mul_pow, Phi_mul_D, one_pow, map_one, mul_one]

/-- `c n j = [x^n] Φ^j`. -/
def c (n j : ℕ) : ℤ := PowerSeries.coeff n (Φ ^ j)

lemma c_eq_sum (n j : ℕ) (hj : 0 < j) :
    c n j = ∑ b ∈ Finset.range (n/2+1),
      ((Nat.choose (2*j-1+(n-2*b)) (2*j-1) : ℕ):ℤ) * ((Nat.choose (j-1+b) (j-1):ℕ):ℤ) := by
  unfold c
  rw [Phi_pow, coeff_mul_expand2]
  apply Finset.sum_congr rfl
  intro b hb
  rw [coeff_invOneSubPow (2*j) (n-2*b) (by omega), coeff_invOneSubPow j b hj]

/-- The OEIS sequence (copied from Spec). -/
def aa (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  Finset.sum (Finset.range (n / 2 + 1)) fun k =>
    ((3 * n - 2 * k - 1).choose (n - 2 * k)) * ((n + k - 1).choose k)

lemma aa_eq_c (n : ℕ) (hn : 0 < n) : (aa n : ℤ) = c n n := by
  rw [c_eq_sum n n hn]
  unfold aa
  rw [if_neg (by omega)]
  push_cast
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.mem_range] at hb
  have hbn : 2 * b ≤ n := by omega
  have e1 : (3*n-2*b-1).choose (n-2*b) = (2*n-1+(n-2*b)).choose (2*n-1) := by
    rw [show 2*n-1+(n-2*b) = 3*n-2*b-1 by omega,
        ← Nat.choose_symm (show 2*n-1 ≤ 3*n-2*b-1 by omega)]
    congr 1; omega
  have e2 : (n+b-1).choose b = (n-1+b).choose (n-1) := by
    rw [show n-1+b = n+b-1 by omega, ← Nat.choose_symm (show n-1 ≤ n+b-1 by omega)]
    congr 1; omega
  rw [e1, e2]

lemma frobenius (p : ℕ) (hp : p ≠ 0) (N J : ℕ) :
    c (N*p) (J*p) = ∑ t ∈ Finset.range (N+1),
      c t J * PowerSeries.coeff (p*(N-t)) ((g p hp)^J) := by
  have hp0 := Nat.pos_of_ne_zero hp
  unfold c
  rw [Nat.mul_comm J p, ← expand_Phi_pow_mul_g_pow p hp J,
      coeff_expand_mul_left p hp (Φ^J) ((g p hp)^J) (N*p),
      Nat.mul_div_cancel N hp0]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.mem_range] at ht
  have he : N*p - p*t = p*(N-t) := by rw [Nat.mul_comm N p, Nat.mul_sub_left_distrib]
  rw [he]

/-- constant coefficient of Φ is 1. -/
lemma coeff0_Phi : PowerSeries.coeff 0 Φ = 1 := by
  unfold Φ
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [coeff_invOneSubPow 2 0 (by norm_num)]
  rw [coeff_expand 2 hp2, if_pos (dvd_zero 2), Nat.zero_div, coeff_invOneSubPow 1 0 (by norm_num)]
  simp

lemma coeff0_D : PowerSeries.coeff 0 D = 1 := by
  unfold D
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  have h2 : PowerSeries.coeff 0 (invOneSubPow ℤ 2).inv = 1 := by
    rw [invOneSubPow_inv_eq_one_sub_pow]; simp
  have h1 : PowerSeries.coeff 0 (invOneSubPow ℤ 1).inv = 1 := by
    rw [invOneSubPow_inv_eq_one_sub_pow]; simp
  rw [h2, coeff_expand 2 hp2, if_pos (dvd_zero 2), Nat.zero_div, h1]; simp

lemma coeff0_g (p : ℕ) (hp : p ≠ 0) : PowerSeries.coeff 0 (g p hp) = 1 := by
  unfold g
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  have hphi : PowerSeries.coeff 0 (Φ ^ p) = 1 := by
    rw [coeff_zero_eq_constantCoeff, map_pow, ← coeff_zero_eq_constantCoeff, coeff0_Phi, one_pow]
  rw [hphi, coeff_expand p hp, if_pos (dvd_zero p), Nat.zero_div, coeff0_D]; simp

lemma coeff0_g_pow (p : ℕ) (hp : p ≠ 0) (M : ℕ) :
    PowerSeries.coeff 0 ((g p hp) ^ M) = 1 := by
  rw [coeff_zero_eq_constantCoeff, map_pow, ← coeff_zero_eq_constantCoeff, coeff0_g, one_pow]

/-- valuation of difference equals the smaller valuation (ultrametric). -/
lemma vp_sub_eq (p : ℕ) [Fact p.Prime] (a b : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hlt : padicValNat p a < padicValNat p b) :
    padicValNat p (b - a) = padicValNat p a := by
  have hane : a ≠ 0 := ha.ne'
  have hba : b - a ≠ 0 := by
    intro h
    have hba' : b = a := by omega
    rw [hba'] at hlt; exact lt_irrefl _ hlt
  have hpσa : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
  have hpσb : p ^ padicValNat p a ∣ b :=
    dvd_trans (pow_dvd_pow p (le_of_lt hlt)) pow_padicValNat_dvd
  have hpσba : p ^ padicValNat p a ∣ (b - a) := Nat.dvd_sub hpσb hpσa
  have hpσ1b : p ^ (padicValNat p a + 1) ∣ b :=
    dvd_trans (pow_dvd_pow p (Nat.succ_le_of_lt hlt)) pow_padicValNat_dvd
  have hnot : ¬ p ^ (padicValNat p a + 1) ∣ (b - a) := by
    intro h
    have : p ^ (padicValNat p a + 1) ∣ a := by
      have h2 := Nat.dvd_sub hpσ1b h
      rwa [Nat.sub_sub_self hab] at h2
    exact (pow_succ_padicValNat_not_dvd hane) this
  have h1 : padicValNat p a ≤ padicValNat p (b - a) := (padicValNat_dvd_iff_le hba).mp hpσba
  have h2 : padicValNat p (b - a) < padicValNat p a + 1 := by
    by_contra hcon; push_neg at hcon
    exact hnot ((padicValNat_dvd_iff_le hba).mpr hcon)
  omega

end
end A352373

namespace A352373
noncomputable section
open PowerSeries

/-- LEMMA A (refined Dwork/Kazandzidis bound). -/
lemma LemA (p : ℕ) (hp_prime : p.Prime) (hp5 : 5 ≤ p) (M' s : ℕ) (hs : 1 ≤ s) :
    (p : ℤ) ^ (3 + padicValNat p s + 2 * padicValNat p M') ∣
      PowerSeries.coeff (p * s) ((g p (by omega) ) ^ M') := by
  sorry

/-- LEMMA B (logarithmic derivative bound). -/
lemma LemB (p : ℕ) (hp_prime : p.Prime) (hp5 : 5 ≤ p) (M' m : ℕ) (hm : 1 ≤ m) (hM' : 1 ≤ M') :
    (p : ℤ) ^ (padicValNat p M' - padicValNat p m) ∣ c m M' := by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  -- the logarithmic-derivative identity:  m * c m M' = M' * (an integer coefficient)
  have key : (m : ℤ) * c m M' =
      (M' : ℤ) * PowerSeries.coeff (m - 1) (Φ ^ (M' - 1) * (PowerSeries.derivative ℤ) Φ) := by
    have hcoeffD : (PowerSeries.coeff (m - 1)) ((PowerSeries.derivative ℤ) (Φ ^ M')) =
        PowerSeries.coeff m (Φ ^ M') * (m : ℤ) := by
      rw [coeff_derivative]
      have hmm : m - 1 + 1 = m := by omega
      rw [hmm]
      congr 1
      omega
    have hleib : (PowerSeries.derivative ℤ) (Φ ^ M') =
        M' • (Φ ^ (M' - 1) * (PowerSeries.derivative ℤ) Φ) := by
      rw [Derivation.leibniz_pow, smul_eq_mul]
    rw [hleib, map_nsmul, nsmul_eq_mul] at hcoeffD
    rw [mul_comm]
    rw [hcoeffD]
    rfl
  -- divisibility extraction
  set α := padicValNat p M' with hα
  set β := padicValNat p m with hβ
  by_cases hc : c m M' = 0
  · rw [hc]; exact dvd_zero _
  · have hmne : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hMdvd : (p : ℤ) ^ α ∣ (M' : ℤ) := by
      have : p ^ α ∣ M' := pow_padicValNat_dvd
      exact_mod_cast this
    have hdvd : (p : ℤ) ^ α ∣ (m : ℤ) * c m M' :=
      dvd_trans hMdvd ⟨_, key⟩
    have hmcne : (m : ℤ) * c m M' ≠ 0 := mul_ne_zero hmne hc
    have hle : α ≤ padicValInt p ((m : ℤ) * c m M') := by
      rcases (padicValInt_dvd_iff α _).mp hdvd with h | h
      · exact absurd h hmcne
      · exact h
    rw [padicValInt.mul hmne hc, padicValInt.of_nat, ← hβ] at hle
    rw [padicValInt_dvd_iff]
    right
    omega

theorem main (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5)
    (n : ℕ) (hn_pos : 0 < n) (k : ℕ) (hk_pos : 0 < k) :
    (aa (n * p ^ k) : ℤ) ≡ aa (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp0 : p ≠ 0 := by omega
  set M := n * p ^ (k - 1) with hMdef
  have hM1 : 1 ≤ M :=
    Nat.one_le_iff_ne_zero.mpr (by rw [hMdef]; exact Nat.mul_ne_zero hn_pos.ne' (pow_ne_zero _ hp0))
  have hMpk : n * p ^ k = M * p := by
    rw [hMdef]; rw [mul_assoc]; congr 1
    rw [← pow_succ]; congr 1; omega
  -- valuation of M is at least k-1
  have hpdvdM : p ^ (k - 1) ∣ M := by rw [hMdef]; exact Dvd.intro_left n rfl
  have he : k - 1 ≤ padicValNat p M := (padicValNat_dvd_iff_le (by omega)).mp hpdvdM
  set e := padicValNat p M with hedef
  -- the difference as a sum
  have hdiff : (aa (n * p ^ k) : ℤ) - (aa (n * p ^ (k - 1)) : ℤ) =
      ∑ t ∈ Finset.range M, c t M * PowerSeries.coeff (p * (M - t)) ((g p hp0) ^ M) := by
    rw [aa_eq_c (n * p ^ k) (by positivity), aa_eq_c (n * p ^ (k - 1)) (by positivity)]
    rw [hMpk, frobenius p hp0 M M]
    rw [Finset.sum_range_succ]
    rw [Nat.sub_self, mul_zero, coeff0_g_pow p hp0, mul_one]
    rw [← hMdef]
    ring
  -- each term divisible by p^(3k)
  have hterm : ∀ t ∈ Finset.range M,
      (p : ℤ) ^ (3 * k) ∣ c t M * PowerSeries.coeff (p * (M - t)) ((g p hp0) ^ M) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    set s := M - t with hsdef
    have hs1 : 1 ≤ s := by omega
    set σ := padicValNat p s with hσdef
    have hcoeff : (p : ℤ) ^ (3 + σ + 2 * e) ∣
        PowerSeries.coeff (p * s) ((g p hp0) ^ M) := by
      have hlemA := LemA p hp_prime hp_ge_5 M s hs1
      exact hlemA
    by_cases hcase : k - 1 ≤ σ
    · -- Case A: use LemA alone
      have hexp : 3 * k ≤ 3 + σ + 2 * e := by omega
      exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow _ hexp) hcoeff) _
    · -- Case B
      push_neg at hcase  -- σ < k-1
      have hσe : σ < e := by omega
      -- t = M - s, and v_p(t) = σ
      have hMs : M - s = t := by rw [hsdef]; omega
      have htval : padicValNat p t = σ := by
        have hh := vp_sub_eq p s M hs1 (by omega) (by rw [← hσdef, ← hedef]; omega)
        rw [hMs] at hh
        rw [hh, ← hσdef]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h1
        · exfalso
          rw [h0] at htval
          simp [padicValNat.zero] at htval
          -- t=0 => s=M => σ = padicValNat p M = e ≥ k-1, contra
          have : s = M := by omega
          rw [this, ← hedef] at hσdef
          omega
        · exact h1
      have hcB : (p : ℤ) ^ (e - σ) ∣ c t M := by
        have := LemB p hp_prime hp_ge_5 M t ht1 hM1
        rw [htval, ← hedef] at this
        exact this
      have hprod : (p : ℤ) ^ ((e - σ) + (3 + σ + 2 * e)) ∣
          c t M * PowerSeries.coeff (p * s) ((g p hp0) ^ M) := by
        rw [pow_add]; exact mul_dvd_mul hcB hcoeff
      have hexp : 3 * k ≤ (e - σ) + (3 + σ + 2 * e) := by omega
      exact dvd_trans (pow_dvd_pow _ hexp) hprod
  have hsum : (p : ℤ) ^ (3 * k) ∣
      ∑ t ∈ Finset.range M, c t M * PowerSeries.coeff (p * (M - t)) ((g p hp0) ^ M) :=
    Finset.dvd_sum hterm
  rw [← hdiff] at hsum
  rw [Int.modEq_iff_dvd]
  rw [← hMdef] at hsum
  rw [show (↑(aa M) : ℤ) - ↑(aa (n * p ^ k)) = -(↑(aa (n * p ^ k)) - ↑(aa M)) by ring]
  exact dvd_neg.mpr hsum

end
end A352373

/--
A352373 Conjecture: the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
hold for all primes p >= 5 and positive integers n and k.
-/
theorem oeis_a352373_supercongruence :
  ∀ (p : ℕ) (hp_prime : p.Prime) (hp_ge_5 : p ≥ 5),
  ∀ (n : ℕ) (hn_pos : 0 < n),
  ∀ (k : ℕ) (hk_pos : 0 < k),
  (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] :=
fun p hp hp5 n hn k hk => A352373.main p hp hp5 n hn k hk
