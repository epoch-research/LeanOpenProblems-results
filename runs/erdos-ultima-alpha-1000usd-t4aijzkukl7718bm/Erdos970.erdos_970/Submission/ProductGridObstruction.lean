import Submission.PrimeCountingDyadicDiscrepancy

/-! A multiplicative-grid obstruction. These are auxiliary results, not a
proof or disproof of Erdős 970. The candidate set {x*y : 1 ≤ x,y ≤ K} can be
covered using o(K) distinct prime residue classes. -/
namespace Erdos970.ProductGrid
open Finset Filter Real
set_option maxHeartbeats 1500000

lemma pow_two_of_no_other_prime (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2) : ∃ e : ℕ, n = 2^e := by
  by_cases hn1 : n = 1
  · exact ⟨0, by simpa using hn1⟩
  obtain ⟨p,hp,hpn⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hn1
  have hp2 := h p hp hpn
  subst p
  have hpow : IsPrimePow n := isPrimePow_iff_unique_prime_dvd.mpr
    ⟨2,⟨Nat.prime_two,hpn⟩,fun q hq => h q hq.1 hq.2⟩
  obtain ⟨q,e,hq,he,hqe⟩ := (isPrimePow_nat_iff n).mp hpow
  have hqn : q ∣ n := by rw [← hqe]; exact dvd_pow_self q he.ne'
  have hq2 := h q hq hqn
  subst q
  exact ⟨e,hqe.symm⟩

lemma bounded_pow_two_or_odd_prime (t n : ℕ) (hn : 0 < n) (hnt : n ≤ 2^t) :
    (∃ e ≤ t, n = 2^e) ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ 2^t ∧ p ∣ n := by
  by_cases h : ∀ p : ℕ, p.Prime → p ∣ n → p = 2
  · obtain ⟨e,rfl⟩ := pow_two_of_no_other_prime n h
    exact Or.inl ⟨e,(Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hnt,rfl⟩
  · push_neg at h
    obtain ⟨p,hp,hpn,hp2⟩ := h
    exact Or.inr ⟨p,hp,hp2,(Nat.le_of_dvd hn hpn).trans hnt,hpn⟩

def core (t : ℕ) : Finset ℕ := ((2^t+1).primesBelow).erase 2

noncomputable def extraPrime (t e : ℕ) : ℕ := Nat.nth Nat.Prime ((2^t)^2+2^t+3+e)

lemma extraPrime_prime (t e : ℕ) : (extraPrime t e).Prime := Nat.prime_nth_prime _

lemma extraPrime_large (t e : ℕ) : 2^t < extraPrime t e := by
  have hh := (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le ((2^t)^2+2^t+3+e)
  change (2^t)^2+2^t+3+e ≤ extraPrime t e at hh
  omega

lemma extraPrime_large_square (t e : ℕ) : (2^t)^2 < extraPrime t e := by
  have hh := (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le ((2^t)^2+2^t+3+e)
  change (2^t)^2+2^t+3+e ≤ extraPrime t e at hh
  nlinarith [Nat.zero_le (2^t)]

lemma extraPrime_injective (t : ℕ) : Function.Injective (extraPrime t) := by
  intro a b hab
  have hh := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
  omega

noncomputable def primes (t : ℕ) : Finset ℕ :=
  core t ∪ (range (2*t+1)).image (extraPrime t)

noncomputable def residues (t p : ℕ) : ℕ :=
  if h : ∃ e : ℕ, e < 2*t+1 ∧ extraPrime t e = p then 2^(Classical.choose h) else 0

lemma residues_extra (t e : ℕ) (he : e < 2*t+1) :
    residues t (extraPrime t e) = 2^e := by
  have h : ∃ d : ℕ, d < 2*t+1 ∧ extraPrime t d = extraPrime t e := ⟨e,he,rfl⟩
  rw [residues,dif_pos h]
  have hh := (extraPrime_injective t) (Classical.choose_spec h).2
  rw [hh]

lemma residues_core (t p : ℕ) (hp : p ∈ core t) : residues t p = 0 := by
  have hplt : p < 2^t+1 := (Nat.mem_primesBelow.mp (mem_of_mem_erase hp)).1
  apply dif_neg
  rintro ⟨e,he,hq⟩
  have hh := extraPrime_large t e
  omega

lemma primes_prime (t : ℕ) : ∀ p ∈ primes t, p.Prime := by
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · exact Nat.prime_of_mem_primesBelow (mem_of_mem_erase hp)
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hp
    exact extraPrime_prime t e

lemma core_card_le (t : ℕ) : (core t).card ≤ (2^t).primeCounting := by
  have hh : (((2^t+1).primesBelow).erase 2).card ≤ ((2^t+1).primesBelow).card := card_erase_le
  simpa only [core,Nat.primesBelow,Nat.primeCounting,Nat.primeCounting',
    Nat.count_eq_card_filter_range] using hh

lemma primes_card_le (t : ℕ) : (primes t).card ≤ (2^t).primeCounting+2*t+1 := by
  have hu := card_union_le (core t) ((range (2*t+1)).image (extraPrime t))
  have hi := card_image_le (s := range (2*t+1)) (f := extraPrime t)
  rw [card_range] at hi
  have hc := core_card_le t
  change (primes t).card ≤ _ at hu
  omega

/-- Every positive product in the square grid is covered. This does not
say that the entire interval up to 4^t is covered. -/
theorem product_grid_cover (t x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxt : x ≤ 2^t) (hyt : y ≤ 2^t) :
    ∃ p ∈ primes t, x*y ≡ residues t p [MOD p] := by
  have odd_factor (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpt : p ≤ 2^t)
      (hpd : p ∣ x*y) : ∃ p ∈ primes t, x*y ≡ residues t p [MOD p] := by
    have hpc : p ∈ core t := mem_erase.mpr
      ⟨hp2,Nat.mem_primesBelow.mpr ⟨by omega,hp⟩⟩
    refine ⟨p,mem_union_left _ hpc,?_⟩
    rw [residues_core t p hpc]
    exact Nat.modEq_zero_iff_dvd.mpr hpd
  rcases bounded_pow_two_or_odd_prime t x hx hxt with ⟨a,ha,hxa⟩ | ⟨p,hp,hp2,hpt,hpd⟩
  · rcases bounded_pow_two_or_odd_prime t y hy hyt with ⟨b,hb,hyb⟩ | ⟨p,hp,hp2,hpt,hpd⟩
    · have hab : a+b < 2*t+1 := by omega
      refine ⟨extraPrime t (a+b),mem_union_right _ (mem_image.mpr
        ⟨a+b,mem_range.mpr hab,rfl⟩),?_⟩
      rw [residues_extra t (a+b) hab,hxa,hyb,← pow_add]
    · exact odd_factor p hp hp2 hpt (dvd_mul_of_dvd_right hpd x)
  · exact odd_factor p hp hp2 hpt (dvd_mul_of_dvd_left hpd y)

/-- Every prime strictly between the grid side and its square survives the
residue sieve. The extra primes exceed the entire candidate interval. -/
lemma prime_survives (t i : ℕ) (hi : i.Prime) (hti : 2^t < i)
    (hi2 : i ≤ (2^t)^2) (ht : 0 < t) :
    ∀ p ∈ primes t, ¬i ≡ residues t p [MOD p] := by
  intro p hp hmod
  have htwo : 2 ≤ 2^t := Nat.le_self_pow ht.ne' 2
  rcases mem_union.mp hp with hp | hp
  · rw [residues_core t p hp] at hmod
    have hpd := Nat.modEq_zero_iff_dvd.mp hmod
    have hpp := Nat.prime_of_mem_primesBelow (mem_of_mem_erase hp)
    have hpi : p = i := (Nat.prime_dvd_prime_iff_eq hpp hi).mp hpd
    have hps : p < 2^t+1 := (Nat.mem_primesBelow.mp (mem_of_mem_erase hp)).1
    omega
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hp
    have het : e < 2*t+1 := mem_range.mp he
    rw [residues_extra t e het] at hmod
    have he2 : 2^e ≤ (2^t)^2 := by
      calc
        2^e ≤ 2^(2*t) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2^t)^2 := by rw [← pow_mul]; congr 1; omega
    have hiq := hi2.trans_lt (extraPrime_large_square t e)
    have heq := he2.trans_lt (extraPrime_large_square t e)
    have hie : i = 2^e := hmod.eq_of_lt_of_lt hiq heq
    have hie2 : i = 2 := by
      exact ((hi.pow_eq_iff).mp hie.symm).1.symm
    omega

/-- The construction always has a survivor by twice the side length, despite
covering the whole multiplicative grid. -/
theorem exists_survivor_le_two_side (t : ℕ) (ht : 0 < t) :
    ∃ i : ℕ, 2^t < i ∧ i ≤ 2*2^t ∧ ∀ p ∈ primes t, ¬i ≡ residues t p [MOD p] := by
  obtain ⟨i,hi,hti,hiu⟩ := Nat.exists_prime_lt_and_le_two_mul (2^t) (by positivity)
  have htwo : 2 ≤ 2^t := Nat.le_self_pow ht.ne' 2
  exact ⟨i,hti,hiu,prime_survives t i hi hti (by nlinarith) ht⟩

/-- The number of distinct primes used is sublinear in the side length. -/
theorem primes_card_density_zero :
    Tendsto (fun t : ℕ => ((primes t).card : ℝ)/(2 : ℝ)^t) atTop (nhds 0) := by
  have ht : Tendsto (fun t : ℕ => 2^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hp := PrimeCountingDyadic.density_tendsto_zero.comp ht
  have hlin := (tendsto_pow_const_div_const_pow_of_one_lt 1
    (by norm_num : (1 : ℝ) < 2)).const_mul 2
  have hone := tendsto_pow_const_div_const_pow_of_one_lt 0
    (by norm_num : (1 : ℝ) < 2)
  have hsum : Tendsto (fun t : ℕ =>
      (((2^t).primeCounting : ℝ)+2*(t : ℝ)+1)/(2 : ℝ)^t) atTop (nhds 0) := by
    convert (hp.add hlin).add hone using 1
    · funext t
      simp only [Function.comp_def,Nat.cast_pow,Nat.cast_ofNat,pow_one,pow_zero]
      ring
    · norm_num
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hsum
  exact Eventually.of_forall (fun t => div_le_div_of_nonneg_right
    (by exact_mod_cast primes_card_le t) (by positivity))

lemma eventually_grid_budget (C : ℕ) :
    ∀ᶠ t : ℕ in atTop, C*(primes t).card ≤ 2^t := by
  by_cases hC : C = 0
  · subst C
    simp
  have hCR : (0 : ℝ) < C := by exact_mod_cast Nat.pos_of_ne_zero hC
  have hh := primes_card_density_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1/(C : ℝ) by positivity))
  filter_upwards [hh] with t ht
  have he := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^t) hCR).mp ht
  have hle : (C : ℝ)*((primes t).card : ℝ) ≤ (2 : ℝ)^t := by nlinarith
  exact_mod_cast hle

lemma primes_card_pos (t : ℕ) : 0 < (primes t).card := by
  apply card_pos.mpr
  exact ⟨extraPrime t 0,mem_union_right _ (mem_image.mpr ⟨0,by simp,rfl⟩)⟩

/-- Convert the genuine prime residue cover to a translated coprimality
example using CRT. The factor count is exactly the number of chosen primes. -/
theorem translated_product_grid_cover (t : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = (primes t).card ∧
      ∃ a : ℤ, ∀ x y : ℕ, 0 < x → 0 < y → x ≤ 2^t → y ≤ 2^t →
        ¬(a+(x*y : ℕ)).natAbs.Coprime n := by
  classical
  let P := primes t
  let n := ∏ p ∈ P, p
  have hP : ∀ p ∈ P, p.Prime := primes_prime t
  have hn : 0 < n := prod_pos (fun p hp => (hP p hp).pos)
  have hcard : n.primeFactors.card = P.card := by
    simp only [n,Nat.primeFactors_prod hP]
  have hco : Set.Pairwise (↑P : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset (residues t) id P
    (fun p hp => (hP p hp).ne_zero) hco
  refine ⟨n,hn,hcard,-(b.val : ℤ),?_⟩
  intro x y hx hy hxt hyt hc
  obtain ⟨p,hp,hxy⟩ := product_grid_cover t x y hx hy hxt hyt
  have hb : b.val ≡ x*y [MOD p] := (b.property p hp).trans hxy.symm
  have hd : (p : ℤ) ∣ -(b.val : ℤ)+(x*y : ℕ) := by
    convert hb.dvd using 1
    ring
  exact Nat.not_coprime_of_dvd_of_dvd (hP p hp).one_lt
    (Int.natCast_dvd.mp hd) (dvd_prod_of_mem id hp) hc

/-- For every fixed linear side multiplier, the bilinear candidate-grid
assertion fails. This does NOT cover all positions in a quadratic interval. -/
theorem no_fixed_linear_product_grid (C : ℕ) :
    ¬∀ k : ℕ, 0 < k → ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
      ∀ a : ℤ, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≤ C*k ∧ y ≤ C*k ∧
        (a+(x*y : ℕ)).natAbs.Coprime n := by
  intro h
  obtain ⟨t,ht⟩ := (eventually_grid_budget C).exists
  obtain ⟨n,hn,hcard,a,ha⟩ := translated_product_grid_cover t
  obtain ⟨x,y,hx,hy,hxk,hyk,hgood⟩ :=
    h (primes t).card (primes_card_pos t) n hn hcard.le a
  exact ha x y hx hy (hxk.trans ht) (hyk.trans ht) hgood

/-- A survivor and the obstructed product grid occur for the SAME translate
and modulus. This explicitly separates the auxiliary obstruction from a
counterexample to a quadratic interval bound. -/
theorem translated_grid_cover_with_survivor (t : ℕ) (ht : 0 < t) :
    ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = (primes t).card ∧ ∃ a : ℤ,
      (∀ x y : ℕ, 0 < x → 0 < y → x ≤ 2^t → y ≤ 2^t →
        ¬(a+(x*y : ℕ)).natAbs.Coprime n) ∧
      (∃ i : ℕ, 2^t < i ∧ i ≤ 2*2^t ∧ (a+i).natAbs.Coprime n) := by
  classical
  let P := primes t
  let n := ∏ p ∈ P, p
  have hP : ∀ p ∈ P, p.Prime := primes_prime t
  have hn : 0 < n := prod_pos (fun p hp => (hP p hp).pos)
  have hcard : n.primeFactors.card = P.card := by
    simp only [n,Nat.primeFactors_prod hP]
  have hco : Set.Pairwise (↑P : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset (residues t) id P
    (fun p hp => (hP p hp).ne_zero) hco
  refine ⟨n,hn,hcard,-(b.val : ℤ),?_,?_⟩
  · intro x y hx hy hxt hyt hc
    obtain ⟨p,hp,hxy⟩ := product_grid_cover t x y hx hy hxt hyt
    have hb : b.val ≡ x*y [MOD p] := (b.property p hp).trans hxy.symm
    have hd : (p : ℤ) ∣ -(b.val : ℤ)+(x*y : ℕ) := by
      convert hb.dvd using 1
      ring
    exact Nat.not_coprime_of_dvd_of_dvd (hP p hp).one_lt
      (Int.natCast_dvd.mp hd) (dvd_prod_of_mem id hp) hc
  · obtain ⟨i,hil,hiu,hi⟩ := exists_survivor_le_two_side t ht
    refine ⟨i,hil,hiu,?_⟩
    apply Nat.Coprime.prod_right
    intro p hp
    apply Nat.Coprime.symm
    apply (hP p hp).coprime_iff_not_dvd.mpr
    intro hpd
    have hd : (p : ℤ) ∣ -(b.val : ℤ)+i := Int.natCast_dvd.mpr hpd
    have hbi : b.val ≡ i [MOD p] := Nat.modEq_of_dvd (by
      convert hd using 1
      ring)
    exact hi p hp (hbi.symm.trans (b.property p hp))

lemma primes_card_lower (t : ℕ) : 2*t+1 ≤ (primes t).card := by
  have hh := card_le_card (subset_union_right (s₁ := core t)
    (s₂ := (range (2*t+1)).image (extraPrime t)))
  rw [card_image_of_injective _ (extraPrime_injective t),card_range] at hh
  exact hh

/-- The failure of the linear-side grid proposal persists beyond every
finite cardinality threshold. -/
theorem arbitrarily_large_grid_counterexamples (C K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ ∃ n : ℕ, 0 < n ∧ n.primeFactors.card = k ∧
      ∃ a : ℤ, ∀ x y : ℕ, 0 < x → 0 < y → x ≤ C*k → y ≤ C*k →
        ¬(a+(x*y : ℕ)).natAbs.Coprime n := by
  obtain ⟨t,ht,hK⟩ := ((eventually_grid_budget C).and (eventually_ge_atTop K)).exists
  obtain ⟨n,hn,hcard,a,ha⟩ := translated_product_grid_cover t
  refine ⟨(primes t).card,?_,primes_card_pos t,n,hn,hcard,a,?_⟩
  · have hh := primes_card_lower t
    omega
  · intro x y hx hy hxk hyk
    exact ha x y hx hy (hxk.trans ht) (hyk.trans ht)

#print axioms product_grid_cover
#print axioms primes_card_density_zero
#print axioms translated_product_grid_cover
#print axioms no_fixed_linear_product_grid
#print axioms translated_grid_cover_with_survivor
#print axioms arbitrarily_large_grid_counterexamples
end Erdos970.ProductGrid
