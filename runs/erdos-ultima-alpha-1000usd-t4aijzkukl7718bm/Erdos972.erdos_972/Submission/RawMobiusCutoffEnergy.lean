import Submission.PolylogPowerDivisorLimit
import Submission.SelbergWeights

/-! Lower bounds for the mean-square mass of the raw truncated Möbius
sum. These diagnose a divisor-tail method, not the prime-pair conjecture. -/
namespace Erdos972RawMobiusCutoffEnergy

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights

set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma prod_one_sub_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hi := ih (fun i hi => h0 i (mem_insert_of_mem hi))
      (fun i hi => h1 i (mem_insert_of_mem hi))
    have hp : (∏ i ∈ s, (1-f i)) ≤ 1 :=
      prod_le_one (fun i hi => sub_nonneg.mpr (h1 i (mem_insert_of_mem hi)))
        (fun i hi => by linarith only [h0 i (mem_insert_of_mem hi)])
    have hfa := h0 a (mem_insert_self a s)
    nlinarith only [hi, hp, hfa]

noncomputable def primeSquareMass (N : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N, if p.Prime then ((p : ℝ)^2)⁻¹ else 0

lemma primeSquareMass_nonneg (N : ℕ) : 0 ≤ primeSquareMass N := by
  apply sum_nonneg
  intro p hp
  split_ifs <;> positivity

lemma primeSquareMass_mono {M N : ℕ} (hMN : M ≤ N) :
    primeSquareMass M ≤ primeSquareMass N := by
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hMN)
  intro p hp _
  split_ifs <;> positivity

lemma primeSquareMass_small : primeSquareMass 40 ≤ (9/20 : ℝ) := by
  norm_num [primeSquareMass, Finset.sum_Ioc_succ_top]

/-- An elementary bound strictly below one half. -/
theorem primeSquareMass_le (N : ℕ) : primeSquareMass N ≤ (12/25 : ℝ) := by
  let M := max N 40
  have h40 : 40 ≤ M := le_max_right _ _
  have he : primeSquareMass M = primeSquareMass 40 +
      ∑ p ∈ Ioc 40 M, if p.Prime then ((p : ℝ)^2)⁻¹ else 0 := by
    symm
    exact sum_Ioc_consecutive _ (by decide) h40
  have ht : (∑ p ∈ Ioc 40 M, if p.Prime then ((p : ℝ)^2)⁻¹ else 0) ≤ 1/40 := by
    calc
      _ ≤ ∑ p ∈ Ioc 40 M, ((p : ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro p hp
        split_ifs
        · exact le_rfl
        · positivity
      _ ≤ (40 : ℝ)⁻¹ - (M : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (by decide) h40
      _ ≤ _ := by have := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) M); linarith
  have hm := primeSquareMass_mono (le_max_left N 40)
  rw [he] at hm
  linarith only [hm, ht, primeSquareMass_small]

lemma totient_ratio_lower {n : ℕ} (hn : 0 < n) :
    1 - ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ ≤ (n.totient : ℝ)/n := by
  have he : (n.totient : ℝ)/n = ∏ p ∈ n.primeFactors, (1-(p : ℝ)⁻¹) := by
    have hh := Nat.totient_eq_mul_prod_factors n
    have hhR : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1-(p : ℝ)⁻¹) := by
      have hx := congrArg (fun x : ℚ => (x : ℝ)) hh
      push_cast at hx
      exact hx
    rw [hhR, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
  rw [he]
  apply prod_one_sub_lower
  · intro p hp
    positivity
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact inv_le_one_of_one_le₀ hp1

noncomputable def squarefreeTotientRatio (n : ℕ) : ℝ :=
  (μ n : ℝ)^2 * ((n.totient : ℝ)/n)

lemma squarefreeTotientRatio_nonneg (n : ℕ) : 0 ≤ squarefreeTotientRatio n := by
  unfold squarefreeTotientRatio
  positivity

noncomputable def squareDefect (N n : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N, if p.Prime ∧ p^2 ∣ n then 1 else 0

noncomputable def totientDefect (N n : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N, if p.Prime ∧ p ∣ n then (p : ℝ)⁻¹ else 0

lemma squareDefect_nonneg (N n : ℕ) : 0 ≤ squareDefect N n := by
  apply sum_nonneg
  intro p hp
  split_ifs <;> positivity

lemma totientDefect_nonneg (N n : ℕ) : 0 ≤ totientDefect N n := by
  apply sum_nonneg
  intro p hp
  split_ifs <;> positivity

lemma totientDefect_eq {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    totientDefect N n = ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ := by
  unfold totientDefect
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, Nat.mem_primeFactors]
  constructor
  · rintro ⟨_, hp, hpn⟩
    exact ⟨hp, hpn, hn.ne'⟩
  · rintro ⟨hp, hpn, _⟩
    exact ⟨⟨hp.pos, (Nat.le_of_dvd hn hpn).trans hnN⟩, hp, hpn⟩

lemma squarefreeTotientRatio_lower {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    1 - squareDefect N n - totientDefect N n ≤ squarefreeTotientRatio n := by
  by_cases hs : Squarefree n
  · have hmu : (μ n : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hs
    rw [squarefreeTotientRatio, hmu, one_mul, totientDefect_eq hn hnN]
    have hl := totient_ratio_lower hn
    linarith only [hl, squareDefect_nonneg N n]
  · obtain ⟨p, hp, hpn⟩ : ∃ p : ℕ, p.Prime ∧ p^2 ∣ n := by
      simpa only [Nat.squarefree_iff_prime_squarefree, not_forall, not_not, exists_prop, pow_two] using hs
    have hpN : p ≤ N := (Nat.le_self_pow (by decide : 2 ≠ 0) p).trans
      ((Nat.le_of_dvd hn hpn).trans hnN)
    have he : (1 : ℝ) ≤ squareDefect N n := by
      have hh := single_le_sum (f := fun q : ℕ => if q.Prime ∧ q^2 ∣ n then (1 : ℝ) else 0)
        (fun q hq => by dsimp only; split_ifs <;> positivity) (mem_Ioc.mpr ⟨hp.pos, hpN⟩)
      simpa only [hp, hpn, and_self, if_true] using hh
    linarith only [he, totientDefect_nonneg N n, squarefreeTotientRatio_nonneg n]

lemma count_multiples_interval {A B d : ℕ} (hAB : A ≤ B) :
    ((Ioc A B).filter (fun n => d ∣ n)).card = B/d - A/d := by
  have he := sum_Ioc_consecutive (fun n : ℕ => if d ∣ n then (1 : ℕ) else 0)
    (Nat.zero_le A) hAB
  simp only [← sum_filter, sum_const, smul_eq_mul, mul_one,
    Nat.Ioc_filter_dvd_card_eq_div] at he
  omega

lemma count_multiples_interval_le {A B d : ℕ} (hAB : A ≤ B) (_hd : 0 < d) :
    (((Ioc A B).filter (fun n => d ∣ n)).card : ℝ) ≤ ((B : ℝ)-A)/d+1 := by
  rw [count_multiples_interval hAB, Nat.cast_sub (Nat.div_le_div_right hAB)]
  have hB : ((B/d : ℕ) : ℝ) ≤ (B : ℝ)/d := Nat.cast_div_le
  have hA : (A : ℝ)/d < (A/d : ℕ)+1 := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using Nat.lt_floor_add_one ((A : ℝ)/d)
  rw [sub_div]
  linarith only [hA, hB]

lemma count_multiples_interval_le_full {A B d : ℕ} :
    (((Ioc A B).filter (fun n => d ∣ n)).card : ℝ) ≤ (B : ℝ)/d := by
  have hs : ((Ioc A B).filter (fun n => d ∣ n)) ⊆ ((Ioc 0 B).filter (fun n => d ∣ n)) := by
    intro n hn
    obtain ⟨hn, hdn⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.zero_le A).trans_lt (mem_Ioc.mp hn).1,
      (mem_Ioc.mp hn).2⟩, hdn⟩
  have hh := Nat.cast_le (α := ℝ).mpr (card_le_card hs)
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hh
  exact hh.trans Nat.cast_div_le

noncomputable def defectRow (A B p : ℕ) : ℝ :=
  (((Ioc A B).filter (fun n => p^2 ∣ n)).card : ℝ) +
    (p : ℝ)⁻¹ * (((Ioc A B).filter (fun n => p ∣ n)).card : ℝ)

lemma defectRow_nonneg (A B p : ℕ) : 0 ≤ defectRow A B p := by
  unfold defectRow
  positivity

lemma defect_sum_eq (A B : ℕ) :
    (∑ n ∈ Ioc A B, (squareDefect B n + totientDefect B n)) =
      ∑ p ∈ Ioc 0 B, if p.Prime then defectRow A B p else 0 := by
  simp only [squareDefect, totientDefect, ← sum_add_distrib]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp only [hprime, true_and, if_true, sum_add_distrib, defectRow]
    rw [← sum_filter, ← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one, mul_comm]
  · simp [hprime]

lemma defectRow_le {A B p : ℕ} (hAB : A ≤ B) (hp : p.Prime) :
    defectRow A B p ≤ 2*((B : ℝ)-A)*((p : ℝ)^2)⁻¹+2 := by
  have hsq := count_multiples_interval_le hAB (pow_pos hp.pos 2)
  have hlin := count_multiples_interval_le hAB hp.pos
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hi : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hh := mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hpR.le)
  rw [Nat.cast_pow] at hsq
  unfold defectRow
  have he : (p : ℝ)⁻¹ * (((B : ℝ)-A)/p+1) = ((B : ℝ)-A)*((p : ℝ)^2)⁻¹+(p : ℝ)⁻¹ := by
    field_simp
  rw [he] at hh
  rw [div_eq_mul_inv] at hsq
  linarith only [hsq, hh, hi]

lemma defectRow_le_full (A B p : ℕ) :
    defectRow A B p ≤ 2*(B : ℝ)*((p : ℝ)^2)⁻¹ := by
  have hsq := count_multiples_interval_le_full (A := A) (B := B) (d := p^2)
  have hlin := count_multiples_interval_le_full (A := A) (B := B) (d := p)
  have hh := mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p))
  rw [Nat.cast_pow, div_eq_mul_inv] at hsq
  have he : (p : ℝ)⁻¹ * ((B : ℝ)/p) = (B : ℝ)*((p : ℝ)^2)⁻¹ := by ring
  rw [he] at hh
  unfold defectRow
  linarith only [hsq, hh]

lemma defect_sum_bound {A B K : ℕ} (hAB : A ≤ B) (hK : 0 < K) (hKB : K ≤ B) :
    (∑ n ∈ Ioc A B, (squareDefect B n + totientDefect B n)) ≤
      (24/25 : ℝ)*((B : ℝ)-A) + 2*K + 2*(B : ℝ)/K := by
  rw [defect_sum_eq, ← sum_Ioc_consecutive _ (Nat.zero_le K) hKB]
  have hlo : (∑ p ∈ Ioc 0 K, if p.Prime then defectRow A B p else 0) ≤
      2*((B : ℝ)-A)*primeSquareMass K + 2*K := by
    calc
      _ ≤ ∑ p ∈ Ioc 0 K,
          (2*((B : ℝ)-A)*(if p.Prime then ((p : ℝ)^2)⁻¹ else 0)+2) := by
        apply sum_le_sum
        intro p hp
        by_cases hprime : p.Prime
        · simpa only [if_pos hprime] using defectRow_le hAB hprime
        · simp only [if_neg hprime, mul_zero, zero_add]
          norm_num
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero,
          nsmul_eq_mul, primeSquareMass]
        ring
  have hhi : (∑ p ∈ Ioc K B, if p.Prime then defectRow A B p else 0) ≤ 2*(B : ℝ)/K := by
    calc
      _ ≤ ∑ p ∈ Ioc K B, 2*(B : ℝ)*((p : ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro p hp
        by_cases hprime : p.Prime
        · simpa only [if_pos hprime] using defectRow_le_full A B p
        · simp only [if_neg hprime]
          positivity
      _ = 2*(B : ℝ)*∑ p ∈ Ioc K B, ((p : ℝ)^2)⁻¹ := by rw [mul_sum]
      _ ≤ 2*(B : ℝ)*((K : ℝ)⁻¹-(B : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub hK.ne' hKB) (by positivity)
      _ ≤ _ := by
        rw [mul_sub, ← div_eq_mul_inv]
        have hh : 0 ≤ 2*(B : ℝ)*(B : ℝ)⁻¹ := by positivity
        linarith only [hh]
  have hmass := mul_le_mul_of_nonneg_left (primeSquareMass_le K)
    (show 0 ≤ 2*((B : ℝ)-A) by exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Nat.cast_le.mpr hAB)))
  linarith only [hlo, hhi, hmass]

/-- Uniform positive mass in the upper half interval; only elementary
square-divisor and totient bounds are used. -/
theorem squarefreeTotientRatio_half_interval {D : ℕ} (hD : 80000 ≤ D) :
    (D : ℝ)/200 ≤ ∑ n ∈ Ioc (D/2) D, squarefreeTotientRatio n := by
  have hhalf : D/2 ≤ D := Nat.div_le_self _ _
  have hlo := sum_le_sum (fun n (hn : n ∈ Ioc (D/2) D) =>
    squarefreeTotientRatio_lower
      ((Nat.zero_le (D/2)).trans_lt (mem_Ioc.mp hn).1) (mem_Ioc.mp hn).2)
  have he : (∑ n ∈ Ioc (D/2) D, (1-squareDefect D n-totientDefect D n)) =
      (D : ℝ)-(D/2 : ℕ)-∑ n ∈ Ioc (D/2) D, (squareDefect D n+totientDefect D n) := by
    simp only [sub_sub, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ioc, Nat.cast_sub hhalf]
  rw [he] at hlo
  have hb := defect_sum_bound (A := D/2) (B := D) (K := 200) hhalf (by decide) (by omega)
  have hfloor : ((D/2 : ℕ) : ℝ) ≤ (D : ℝ)/2 := by exact_mod_cast (Nat.cast_div_le (m := D) (n := 2) (α := ℝ))
  have hDR : (80000 : ℝ) ≤ D := by exact_mod_cast hD
  norm_num only [Nat.cast_ofNat] at hb
  linarith only [hlo, hb, hfloor, hDR]

lemma sum_multiples_upper_half {D r : ℕ} (hr : r ∈ Ioc (D/2) D) (w : ℕ → ℝ) :
    (∑ d ∈ Ioc 0 D, if r ∣ d then w d/d else 0) = w r/r := by
  have hr0 : 0 < r := (Nat.zero_le (D/2)).trans_lt (mem_Ioc.mp hr).1
  rw [sum_eq_single r]
  · simp
  · intro d hd hne
    have hd0 := (mem_Ioc.mp hd).1
    have hrlo := (mem_Ioc.mp hr).1
    apply if_neg
    intro hrd
    obtain ⟨k, hk⟩ := hrd
    have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; omega
    have hk1 : k ≠ 1 := by intro ho; simp [ho] at hk; exact hne hk
    have hk2 : 2 ≤ k := by omega
    have hr2 : D < 2*r := by omega
    have hdD := (mem_Ioc.mp hd).2
    nlinarith only [hk, hk2, hr0, hr2, hdD]
  · intro hnot
    exact (hnot (mem_Ioc.mpr ⟨hr0, (mem_Ioc.mp hr).2⟩)).elim

/-- The raw Möbius quadratic mean has a cutoff-independent positive lower
bound once the cutoff is large. -/
theorem quadraticMain_mobius_lower {D : ℕ} (hD : 80000 ≤ D) :
    (1/200 : ℝ) ≤ quadraticMain D (fun d => (μ d : ℝ)) := by
  have hD0 : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hmass := squarefreeTotientRatio_half_interval hD
  have hsum : (1/200 : ℝ) ≤ ∑ r ∈ Ioc (D/2) D, squarefreeTotientRatio r/(D : ℝ) := by
    rw [← sum_div]
    exact (le_div_iff₀ hD0).mpr (by linarith only [hmass])
  apply hsum.trans
  rw [quadraticMain_diagonal]
  calc
    _ ≤ ∑ r ∈ Ioc (D/2) D,
        (r.totient : ℝ) * (∑ d ∈ Ioc 0 D, if r ∣ d then (μ d : ℝ)/d else 0)^2 := by
      apply sum_le_sum
      intro r hr
      rw [sum_multiples_upper_half hr]
      have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr ((Nat.zero_le (D/2)).trans_lt (mem_Ioc.mp hr).1)
      have hrD : (r : ℝ) ≤ D := Nat.cast_le.mpr (mem_Ioc.mp hr).2
      calc
        _ ≤ squarefreeTotientRatio r/(r : ℝ) :=
          div_le_div_of_nonneg_left (squarefreeTotientRatio_nonneg r) hr0 hrD
        _ = _ := by unfold squarefreeTotientRatio; ring
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        exact mem_Ioc.mpr ⟨(Nat.zero_le (D/2)).trans_lt (mem_Ioc.mp hr).1, (mem_Ioc.mp hr).2⟩
      · intro r hr hnot
        positivity

#print axioms primeSquareMass_le
#print axioms squarefreeTotientRatio_lower
#print axioms squarefreeTotientRatio_half_interval
#print axioms quadraticMain_mobius_lower

end Erdos972RawMobiusCutoffEnergy
