import FormalConjecturesUtil

/-! An explicit failure of logarithmic diagonal domination in a numerically
ordered finite-prime-set model. This is not the complete largest-prime-factor
sequence and does not disprove Erdős 371. -/
namespace Erdos371.NumericalPrimeSetLogEnergyObstruction
open Finset
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def primes : Finset ℕ := {7817, 8389, 8719, 9257, 9337, 10141, 10243, 17123, 25583, 29531, 63839, 68399, 72959, 128981, 234511, 390851}
private lemma prime_7817 : Nat.Prime 7817 := by norm_num
private lemma prime_8389 : Nat.Prime 8389 := by norm_num
private lemma prime_8719 : Nat.Prime 8719 := by norm_num
private lemma prime_9257 : Nat.Prime 9257 := by norm_num
private lemma prime_9337 : Nat.Prime 9337 := by norm_num
private lemma prime_10141 : Nat.Prime 10141 := by norm_num
private lemma prime_10243 : Nat.Prime 10243 := by norm_num
private lemma prime_17123 : Nat.Prime 17123 := by norm_num
private lemma prime_25583 : Nat.Prime 25583 := by norm_num
private lemma prime_29531 : Nat.Prime 29531 := by norm_num
private lemma prime_63839 : Nat.Prime 63839 := by norm_num
private lemma prime_68399 : Nat.Prime 68399 := by norm_num
private lemma prime_72959 : Nat.Prime 72959 := by norm_num
private lemma prime_128981 : Nat.Prime 128981 := by norm_num
private lemma prime_234511 : Nat.Prime 234511 := by norm_num
private lemma prime_390851 : Nat.Prime 390851 := by norm_num
private lemma primes_prime (p : ℕ) (hp : p ∈ primes) : p.Prime := by
  simp only [primes,mem_insert,mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_7817
  · exact prime_8389
  · exact prime_8719
  · exact prime_9257
  · exact prime_9337
  · exact prime_10141
  · exact prime_10243
  · exact prime_17123
  · exact prime_25583
  · exact prime_29531
  · exact prime_63839
  · exact prime_68399
  · exact prime_72959
  · exact prime_128981
  · exact prime_234511
  · exact prime_390851

def label (n : ℕ) : ℕ := max 1 ((primes.filter fun p => p ∣ n).sup id)
lemma label_mul (a b : ℕ) : label (a*b) = max (label a) (label b) := by
  have he : (primes.filter fun p => p ∣ a*b) =
      (primes.filter fun p => p ∣ a) ∪ (primes.filter fun p => p ∣ b) := by
    ext p
    by_cases hp : p ∈ primes
    · simp only [mem_filter,mem_union,hp,true_and,(primes_prime p hp).dvd_mul]
    · simp [hp]
  unfold label
  rw [he,sup_union]
  omega

lemma label_eq_of_selected_prime (p : ℕ) (hp : p ∈ primes) : label p = p := by
  have hprime := primes_prime p hp
  have hu : (primes.filter fun q => q ∣ p).sup id ≤ p := by
    apply Finset.sup_le
    intro q hq
    exact Nat.le_of_dvd hprime.pos (mem_filter.mp hq).2
  have hl : p ≤ (primes.filter fun q => q ∣ p).sup id :=
    le_sup (f := id) (mem_filter.mpr ⟨hp,dvd_refl p⟩)
  unfold label
  rw [le_antisymm hu hl,max_eq_right hprime.one_lt.le]

def loser (n : ℕ) : ℕ := min (label (n+1)) (label (n+2))
def sign (n : ℕ) : ℤ :=
  if label (n+1) < label (n+2) then 1 else
    if label (n+2) < label (n+1) then -1 else 0

def groupSum (p N : ℕ) : ℤ := ∑ n ∈ range N, if loser n=p then sign n else 0
def energy (N : ℕ) : ℤ := ∑ p ∈ insert 1 primes, (p : ℤ)*(groupSum p N)^2
def diagonal (N : ℕ) : ℤ := ∑ n ∈ range N, (loser n : ℤ)*(sign n)^2

private def multiples (N : ℕ) : Finset ℕ :=
  primes.biUnion fun p => (range ((N+1)/p+1)).image fun k => p*k
private def sparseEdges (N : ℕ) : Finset ℕ :=
  (((multiples N).image fun r => r-1) ∪
    ((multiples N).image fun r => r-2)).filter fun n => n<N

private lemma label_ne_one_has_divisor (m : ℕ) (hm : label m ≠ 1) :
    ∃ p ∈ primes, p ∣ m := by
  by_contra h
  have he : (primes.filter fun p => p ∣ m) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h ⟨p,(mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  apply hm
  simp [label,he]

private lemma mem_multiples (N m p : ℕ) (hp : p ∈ primes)
    (hm : m≤N+1) (hd : p ∣ m) : m ∈ multiples N := by
  apply mem_biUnion.mpr
  refine ⟨p,hp,mem_image.mpr ⟨m/p,mem_range.mpr ?_,Nat.mul_div_cancel' hd⟩⟩
  have hh := Nat.div_le_div_right hm (c := p)
  omega

private lemma sign_zero_outside (N n : ℕ) (hn : n<N) (hout : n ∉ sparseEdges N) :
    sign n = 0 := by
  have ha : label (n+1)=1 := by
    by_contra h
    obtain ⟨p,hp,hd⟩ := label_ne_one_has_divisor (n+1) h
    have hm := mem_multiples N (n+1) p hp (by omega) hd
    apply hout
    apply mem_filter.mpr
    exact ⟨mem_union_left _ (mem_image.mpr ⟨n+1,hm,by omega⟩),hn⟩
  have hb : label (n+2)=1 := by
    by_contra h
    obtain ⟨p,hp,hd⟩ := label_ne_one_has_divisor (n+2) h
    have hm := mem_multiples N (n+2) p hp (by omega) hd
    apply hout
    apply mem_filter.mpr
    exact ⟨mem_union_right _ (mem_image.mpr ⟨n+2,hm,by omega⟩),hn⟩
  simp [sign,ha,hb]

private lemma range_sum_eq_sparse (N : ℕ) (f : ℕ → ℤ)
    (hf : ∀ n, sign n=0 → f n=0) :
    (∑ n ∈ range N, f n) = ∑ n ∈ sparseEdges N, f n := by
  symm
  apply sum_subset
  · intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  · intro n hn hout
    exact hf n (sign_zero_outside N n (mem_range.mp hn) hout)

private lemma groupSum_sparse (p N : ℕ) : groupSum p N =
    ∑ n ∈ sparseEdges N, if loser n=p then sign n else 0 := by
  exact range_sum_eq_sparse N _ (fun n hn => by simp [hn])
private lemma diagonal_sparse (N : ℕ) : diagonal N =
    ∑ n ∈ sparseEdges N, (loser n : ℤ)*(sign n)^2 := by
  exact range_sum_eq_sparse N _ (fun n hn => by simp [hn])

private lemma label_mem_and_dvd (m : ℕ) : label m ∈ insert 1 primes ∧ label m ∣ m := by
  by_cases hs : (primes.filter fun p => p ∣ m).Nonempty
  · obtain ⟨q,hq,he⟩ := exists_mem_eq_sup _ hs id
    have hqm := (mem_filter.mp hq).1
    have hqp := primes_prime q hqm
    have hl : label m=q := by
      unfold label
      rw [he]
      exact max_eq_right hqp.one_lt.le
    rw [hl]
    exact ⟨mem_insert_of_mem hqm,(mem_filter.mp hq).2⟩
  · have he := not_nonempty_iff_eq_empty.mp hs
    have hl : label m=1 := by simp [label,he]
    simp [hl]

private lemma loser_mem (n : ℕ) : loser n ∈ insert 1 primes := by
  by_cases h : label (n+1) ≤ label (n+2)
  · simpa only [loser,min_eq_left h] using (label_mem_and_dvd (n+1)).1
  · simpa only [loser,min_eq_right (not_le.mp h).le] using (label_mem_and_dvd (n+2)).1

private lemma loser_dvd (n p : ℕ) (h : loser n=p) : p ∣ n+1 ∨ p ∣ n+2 := by
  by_cases hl : label (n+1) ≤ label (n+2)
  · have he : label (n+1)=p := by simpa only [loser,min_eq_left hl] using h
    exact Or.inl (he ▸ (label_mem_and_dvd (n+1)).2)
  · have he : label (n+2)=p := by simpa only [loser,min_eq_right (not_le.mp hl).le] using h
    exact Or.inr (he ▸ (label_mem_and_dvd (n+2)).2)

private def primeEdges (p N : ℕ) : Finset ℕ :=
  (((range ((N+1)/p+1)).image fun k => p*k-1) ∪
    ((range ((N+1)/p+1)).image fun k => p*k-2)).filter fun n => n<N

private lemma mem_primeEdges (p N n : ℕ) (hn : n<N) (hl : loser n=p) :
    n ∈ primeEdges p N := by
  apply mem_filter.mpr
  refine ⟨?_,hn⟩
  rcases loser_dvd n p hl with h | h
  · have hdiv := Nat.div_le_div_right (c := p) (by omega : n+1≤N+1)
    exact mem_union_left _ (mem_image.mpr ⟨(n+1)/p,mem_range.mpr (by omega),by
      rw [Nat.mul_div_cancel' h]; omega⟩)
  · have hdiv := Nat.div_le_div_right (c := p) (by omega : n+2≤N+1)
    exact mem_union_right _ (mem_image.mpr ⟨(n+2)/p,mem_range.mpr (by omega),by
      rw [Nat.mul_div_cancel' h]; omega⟩)

private lemma prime_sum_sparse (p N : ℕ) (f : ℕ → ℤ) :
    (∑ n ∈ range N, if loser n=p then f n else 0) =
      ∑ n ∈ primeEdges p N, if loser n=p then f n else 0 := by
  symm
  apply sum_subset
  · intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  · intro n hn hout
    rw [if_neg (fun h => hout (mem_primeEdges p N n (mem_range.mp hn) h))]

private def fiberWeight (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, if loser n=p then (sign n)^2 else 0

private lemma fiberWeight_sparse (p N : ℕ) : fiberWeight p N =
    ∑ n ∈ primeEdges p N, if loser n=p then (sign n)^2 else 0 :=
  prime_sum_sparse p N _

private lemma diagonal_fiber_formula (N : ℕ) : diagonal N =
    ∑ p ∈ insert 1 primes, (p : ℤ)*fiberWeight p N := by
  symm
  unfold fiberWeight
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp only [mul_ite,mul_zero]
  rw [sum_ite_eq,if_pos (loser_mem n)]

private lemma sparseEdges_card_bound (N : ℕ) :
    (sparseEdges N).card ≤ 2*(∑ p ∈ primes, ((N+1)/p+1)) := by
  have hm : (multiples N).card ≤ ∑ p ∈ primes, ((N+1)/p+1) := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro p hp
    exact (card_image_le).trans_eq (card_range _)
  have h1 := card_image_le (s := multiples N) (f := fun r => r-1)
  have h2 := card_image_le (s := multiples N) (f := fun r => r-2)
  have hu := card_union_le ((multiples N).image fun r => r-1)
    ((multiples N).image fun r => r-2)
  have hf := card_filter_le (s := ((multiples N).image fun r => r-1) ∪
    ((multiples N).image fun r => r-2)) (p := fun n => n<N)
  change (sparseEdges N).card ≤ _ at hf
  omega

private lemma sign_sq_le_one (n : ℕ) : (sign n)^2 ≤ 1 := by
  unfold sign
  split_ifs <;> norm_num

private lemma fiberWeight_one_bound (N : ℕ) :
    fiberWeight 1 N ≤ 2*(∑ p ∈ primes, ((N+1)/p+1) : ℕ) := by
  have he : fiberWeight 1 N =
      ∑ n ∈ sparseEdges N, if loser n=1 then (sign n)^2 else 0 :=
    range_sum_eq_sparse N _ (fun n hn => by simp [hn])
  rw [he]
  have ht : (∑ n ∈ sparseEdges N, if loser n=1 then (sign n)^2 else 0) ≤
      (sparseEdges N).card := by
    calc
      _ ≤ ∑ n ∈ sparseEdges N, (1 : ℤ) := by
        apply sum_le_sum
        intro n hn
        split_ifs
        · exact sign_sq_le_one n
        · norm_num
      _ = _ := by simp
  apply ht.trans
  exact_mod_cast sparseEdges_card_bound N

attribute [irreducible] groupSum fiberWeight

lemma selected_group_value : groupSum 7817 390850 = 15 := by
  rw [groupSum,prime_sum_sparse]
  decide +kernel

private lemma fiber_7817 : fiberWeight 7817 390850 = 15 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_8389 : fiberWeight 8389 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_8719 : fiberWeight 8719 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_9257 : fiberWeight 9257 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_9337 : fiberWeight 9337 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_10141 : fiberWeight 10141 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_10243 : fiberWeight 10243 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_17123 : fiberWeight 17123 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_25583 : fiberWeight 25583 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_29531 : fiberWeight 29531 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_63839 : fiberWeight 63839 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_68399 : fiberWeight 68399 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_72959 : fiberWeight 72959 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_128981 : fiberWeight 128981 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_234511 : fiberWeight 234511 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fiber_390851 : fiberWeight 390851 390850 = 0 := by
  rw [fiberWeight_sparse]
  decide +kernel

private lemma fibers_on_primes (p : ℕ) (hp : p ∈ primes) :
    fiberWeight p 390850 = if p=7817 then 15 else 0 := by
  simp only [primes,mem_insert,mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using fiber_7817
  · simpa using fiber_8389
  · simpa using fiber_8719
  · simpa using fiber_9257
  · simpa using fiber_9337
  · simpa using fiber_10141
  · simpa using fiber_10243
  · simpa using fiber_17123
  · simpa using fiber_25583
  · simpa using fiber_29531
  · simpa using fiber_63839
  · simpa using fiber_68399
  · simpa using fiber_72959
  · simpa using fiber_128981
  · simpa using fiber_234511
  · simpa using fiber_390851

private lemma diagonal_affine : diagonal 390850 = fiberWeight 1 390850+117255 := by
  have hs : (∑ p ∈ primes, (p : ℤ)*fiberWeight p 390850) = 117255 := by
    calc
      _ = ∑ p ∈ primes, if p=7817 then (7817 : ℤ)*15 else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [fibers_on_primes p hp]
        by_cases h : p=7817
        · subst p; simp
        · simp [h]
      _ = _ := by
        rw [sum_ite_eq',if_pos (by decide +kernel : 7817 ∈ primes)]
        norm_num
  rw [diagonal_fiber_formula,sum_insert (by decide +kernel : 1 ∉ primes),hs,Nat.cast_one,one_mul]

lemma diagonal_upper_bound : diagonal 390850 ≤ 118027 := by
  have h := fiberWeight_one_bound 390850
  have hc : (∑ p ∈ primes, ((390850+1)/p+1)) = 386 := by decide +kernel
  rw [hc] at h
  rw [diagonal_affine]
  norm_num at h
  omega

lemma diagonal_nonneg (N : ℕ) : 0≤diagonal N := by unfold diagonal; positivity

lemma energy_lower_bound : 1758825 ≤ energy 390850 := by
  have hp : 7817 ∈ insert 1 primes := by decide +kernel
  have h := single_le_sum (s := insert 1 primes)
    (f := fun p : ℕ => (p : ℤ)*(groupSum p 390850)^2)
    (fun p _ => by positivity) hp
  change (7817 : ℤ)*(groupSum 7817 390850)^2 ≤ energy 390850 at h
  rw [selected_group_value] at h
  have hv : (7817 : ℤ)*15^2 = 1758825 := by norm_num
  rw [hv] at h
  exact h

lemma log_endpoint_lt_fourteen : Real.log (390850 : ℝ) < 14 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ)<390850)
    (by norm_num : (390850 : ℝ)≤2^19)
  rw [Real.log_pow] at h
  have htwo := Real.log_two_lt_d9
  norm_num at h
  linarith

/-- A logarithmic-loss inequality with constant one is false even for a
numerically ordered gapped prime model. This does not address the full set
of primes occurring in Nat.maxPrimeFac. -/
theorem logarithmic_energy_bound_fails :
    Real.log (390850 : ℝ)*(diagonal 390850 : ℝ) < (energy 390850 : ℝ) := by
  have he : (1758825 : ℝ) ≤ energy 390850 := by exact_mod_cast energy_lower_bound
  have hd : (diagonal 390850 : ℝ) ≤ 118027 := by exact_mod_cast diagonal_upper_bound
  have hd0 : (0 : ℝ) ≤ diagonal 390850 := by exact_mod_cast diagonal_nonneg 390850
  have hl := mul_le_mul_of_nonneg_right log_endpoint_lt_fourteen.le hd0
  nlinarith

#print axioms label_mul
#print axioms label_eq_of_selected_prime
#print axioms selected_group_value
#print axioms diagonal_upper_bound
#print axioms logarithmic_energy_bound_fails
end Erdos371.NumericalPrimeSetLogEnergyObstruction
