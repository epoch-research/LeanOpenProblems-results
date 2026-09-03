import FormalConjecturesUtil

/-!
Elementary finite-prime-block variance bounds. These concern integers in finite
prefixes and make no cube-Sidon assertion.
-/
namespace Erdos1206.PrimeBlockVariance
open Finset
open scoped Classical

noncomputable def indicator (p n : ℕ) : ℝ := if p ∣ n then 1 else 0

noncomputable def centered (p n : ℕ) : ℝ := indicator p n - 1/(p:ℝ)

noncomputable def covariance (N p q : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, centered p n * centered q n

lemma sum_indicator (N p : ℕ) :
    (∑ n ∈ Icc 1 N, indicator p n) = (N/p : ℕ) := by
  simp only [indicator, sum_boole]
  have he : (Icc 1 N).filter (fun n => p ∣ n) =
      (range (N+1)).filter (fun n => n ≠ 0 ∧ p ∣ n) := by
    ext n
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [he,Nat.card_multiples']

lemma sum_indicator_mul {p q : ℕ} (hcop : Nat.Coprime p q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, indicator p n * indicator q n) = (N/(p*q) : ℕ) := by
  have hd (n : ℕ) : p*q ∣ n ↔ p ∣ n ∧ q ∣ n :=
    ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩,
      fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  have he (n : ℕ) : indicator p n * indicator q n = indicator (p*q) n := by
    simp only [indicator, hd]
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_indicator N (p*q)

lemma covariance_distinct {p q : ℕ} (hcop : Nat.Coprime p q) (N : ℕ) :
    covariance N p q = (N/(p*q) : ℕ) - (N/p : ℕ)/(q:ℝ) -
      (N/q : ℕ)/(p:ℝ) + (N:ℝ)/((p:ℝ)*q) := by
  have he (n : ℕ) : centered p n * centered q n =
      indicator p n * indicator q n - indicator p n/(q:ℝ) -
        indicator q n/(p:ℝ) + 1/((p:ℝ)*q) := by
    dsimp [centered]
    ring
  simp only [covariance,he,sum_add_distrib,sum_sub_distrib,←sum_div,
    sum_indicator_mul hcop,sum_indicator,sum_const,Nat.card_Icc,
    Nat.add_sub_cancel,nsmul_eq_mul]
  ring

lemma quotient_error {d : ℕ} (hd : 0 < d) (N : ℕ) :
    -1 ≤ (N/d : ℕ) - (N:ℝ)/d ∧ (N/d : ℕ) - (N:ℝ)/d ≤ 0 := by
  have hupper : ((N/d : ℕ):ℝ) ≤ (N:ℝ)/d := Nat.cast_div_le
  have hnat : N < (N/d+1)*d := by simpa [mul_comm] using Nat.lt_mul_div_succ N hd
  have hreal : (N:ℝ) < (((N/d : ℕ):ℝ)+1)*d := by exact_mod_cast hnat
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hlower : (N:ℝ)/d < (N/d : ℕ)+1 := (div_lt_iff₀ hdR).mpr hreal
  constructor <;> linarith

lemma covariance_abs_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (N : ℕ) : |covariance N p q| ≤ 3 := by
  obtain ⟨hpL,hpU⟩ := quotient_error hp N
  obtain ⟨hqL,hqU⟩ := quotient_error hq N
  obtain ⟨hpqL,hpqU⟩ := quotient_error (Nat.mul_pos hp hq) N
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hpinv : 0 ≤ (1:ℝ)/p ∧ (1:ℝ)/p ≤ 1 :=
    ⟨by positivity, (div_le_one hpR).mpr hp1⟩
  have hqinv : 0 ≤ (1:ℝ)/q ∧ (1:ℝ)/q ≤ 1 :=
    ⟨by positivity, (div_le_one hqR).mpr hq1⟩
  have he : covariance N p q =
      ((N/(p*q):ℕ)-(N:ℝ)/(p*q:ℕ)) -
      ((N/p:ℕ)-(N:ℝ)/p)*(1/(q:ℝ)) -
      ((N/q:ℕ)-(N:ℝ)/q)*(1/(p:ℝ)) := by
    rw [covariance_distinct hcop]
    push_cast
    ring
  rw [he]
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hpU hqinv.1
  have h₂ := mul_nonpos_of_nonpos_of_nonneg hqU hpinv.1
  have h₃ := mul_le_mul_of_nonneg_right hpL hqinv.1
  have h₄ := mul_le_mul_of_nonneg_right hqL hpinv.1
  apply abs_le.mpr
  constructor <;> nlinarith only [hpqL,hpqU,h₁,h₂,h₃,h₄,hpinv.2,hqinv.2]

lemma covariance_self_le {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    covariance N p p ≤ (N:ℝ)/p := by
  have he (n : ℕ) : centered p n * centered p n =
      indicator p n * (1-2/(p:ℝ)) + 1/(p:ℝ)^2 := by
    dsimp [centered,indicator]
    split_ifs <;> ring
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hcoef : 0 ≤ 1-2/(p:ℝ) := by
    have := (div_le_one hpR).mpr hp2
    linarith
  have hdiv : ((N/p : ℕ):ℝ) ≤ (N:ℝ)/p := Nat.cast_div_le
  simp only [covariance,he,sum_add_distrib,←sum_mul,sum_indicator,
    sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  calc
    _ ≤ ((N:ℝ)/p)*(1-2/(p:ℝ)) + N*(1/(p:ℝ)^2) := by gcongr
    _ = (N:ℝ)/p - N/(p:ℝ)^2 := by ring
    _ ≤ (N:ℝ)/p := sub_le_self _ (by positivity)

noncomputable def primeSum (P : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, w p * indicator p n

noncomputable def mean (P : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, w p / p

noncomputable def variance (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, (primeSum P w n - mean P w)^2

lemma centered_primeSum (P : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) :
    primeSum P w n - mean P w = ∑ p ∈ P, w p * centered p n := by
  simp only [primeSum,mean,←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  dsimp [centered]
  ring

lemma variance_expand (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ) :
    variance N P w = ∑ p ∈ P, ∑ q ∈ P, w p * w q * covariance N p q := by
  simp only [variance,centered_primeSum,pow_two,sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro q hq
  simp only [covariance,mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

/-- The off-diagonal error is at most three times the square of the number
of primes. In particular, it does not depend on their product. -/
theorem variance_le (N : ℕ) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hw : ∀ p ∈ P, |w p| ≤ 1) :
    variance N P w ≤ (N:ℝ)*(∑ p ∈ P, w p^2/p) + 3*(P.card:ℝ)^2 := by
  rw [variance_expand]
  have hterm (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      w p*w q*covariance N p q ≤
        (if p=q then (N:ℝ)*w p^2/p else 0)+3 := by
    by_cases he : p=q
    · subst q
      rw [if_pos rfl]
      have hh := mul_le_mul_of_nonneg_left (covariance_self_le (hP p hp).two_le N)
        (sq_nonneg (w p))
      calc
        _ = w p^2*covariance N p p := by ring
        _ ≤ w p^2*((N:ℝ)/p) := hh
        _ = (N:ℝ)*w p^2/p := by ring
        _ ≤ (N:ℝ)*w p^2/p+3 := by linarith
    · rw [if_neg he,zero_add]
      have hc := covariance_abs_le (hP p hp).pos (hP q hq).pos
        ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr he) N
      have hab : |w p| * |w q| ≤ 1 := by
        simpa using mul_le_mul (hw p hp) (hw q hq) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      calc
        _ ≤ |w p*w q*covariance N p q| := le_abs_self _
        _ = (|w p| * |w q|)* |covariance N p q| := by rw [abs_mul,abs_mul]
        _ ≤ 1*3 := mul_le_mul hab hc (abs_nonneg _) (by norm_num)
        _ = 3 := by norm_num
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((if p=q then (N:ℝ)*w p^2/p else 0)+3) :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq => hterm p hp q hq))
    _ = _ := by
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
      have he (p : ℕ) (hp : p ∈ P) :
          (∑ q ∈ P, if p=q then (N:ℝ)*w p^2/p else 0) = (N:ℝ)*w p^2/p := by
        simp [hp]
      simp only [sum_congr rfl he]
      rw [mul_sum]
      have he' : (∑ p ∈ P, (N:ℝ)*w p^2/p) = ∑ p ∈ P, (N:ℝ)*(w p^2/p) := by
        apply sum_congr rfl
        intros
        ring
      rw [he']
      ring

/-- A prefix-uniform second moment for a block of primes not exceeding T. -/
theorem variance_le_of_small_primes {N T : ℕ} (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ T) (hw : ∀ p ∈ P, |w p| ≤ 1)
    (hT : T^2 ≤ N) :
    variance N P w ≤ (N:ℝ)*((∑ p ∈ P, w p^2/p)+3) := by
  have hsub : P ⊆ Icc 1 T := fun p hp => mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2⟩
  have hcard : P.card ≤ T := by simpa using card_le_card hsub
  have hcardR : (P.card:ℝ) ≤ T := by exact_mod_cast hcard
  have hTR : (T:ℝ)^2 ≤ N := by exact_mod_cast hT
  have hs : (P.card:ℝ)^2 ≤ N :=
    (pow_le_pow_left₀ (by positivity) hcardR 2).trans hTR
  have hh := variance_le N P w (fun p hp => (hP p hp).1) hw
  nlinarith

#print axioms variance_le
#print axioms variance_le_of_small_primes

#print axioms covariance_abs_le
#print axioms covariance_self_le
end Erdos1206.PrimeBlockVariance
