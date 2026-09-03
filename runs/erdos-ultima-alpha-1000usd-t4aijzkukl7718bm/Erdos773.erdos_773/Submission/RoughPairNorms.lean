import Submission.PrimorialSquareSieve
import Submission.PrimeResidueRotation

/-!
A finite extraction avoiding odd prime factors in pairwise norms.
This is not a Sidon extraction: explicit nontrivial collisions survive
arbitrarily prescribed finite sets of excluded odd primes.
-/
namespace Erdos773.RoughPairNorms
open Finset
set_option maxHeartbeats 1000000

/-- Orient a nonzero square residue against its negative. -/
def localColor (p n : ℕ) : Bool :=
  decide (((n : ZMod p)^2).val < (-((n : ZMod p)^2)).val)

lemma localColor_avoids {p a b : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (ha : ¬p ∣ a) (he : localColor p a = localColor p b) :
    ¬p ∣ a^2+b^2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 :=
    fun hz => ha ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact (not_le_of_gt hp2) (Nat.le_of_dvd (by decide) hd)
  have hne : ((a : ZMod p)^2).val ≠ (-((a : ZMod p)^2)).val := by
    intro hh
    have hh' : (a : ZMod p)^2 = -((a : ZMod p)^2) := ZMod.val_injective p hh
    have hzero : (2 : ZMod p)*(a : ZMod p)^2=0 := by linear_combination hh'
    exact (mul_ne_zero htwo (pow_ne_zero _ ha0)) hzero
  intro hd
  have hz : (a : ZMod p)^2+(b : ZMod p)^2=0 := by
    have hh := (ZMod.natCast_eq_zero_iff (a^2+b^2) p).mpr hd
    simpa using hh
  have hab : (b : ZMod p)^2 = -((a : ZMod p)^2) := eq_neg_of_add_eq_zero_right hz
  simp only [localColor, hab, neg_neg, decide_eq_decide] at he
  omega

/-- One class of at most `2^|P|` colors has pairwise norms coprime to all
primes in P. Repeated pairs are included. The carrier must consist of units
at the excluded primes. -/
theorem finite_extraction (A P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    (hunit : ∀ a ∈ A, ∀ p ∈ P, ¬p ∣ a) :
    ∃ B ⊆ A, A.card ≤ 2^P.card*B.card ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ p ∈ P, ¬p ∣ a^2+b^2 := by
  classical
  let f : ℕ → (P → Bool) := fun n p => localColor p.val n
  have hf : ∀ a ∈ A, f a ∈ (univ : Finset (P → Bool)) := by simp
  have ht : (univ : Finset (P → Bool)).Nonempty := ⟨fun _ => false, mem_univ _⟩
  have hk : (0 : ℝ) < Fintype.card (P → Bool) := by positivity
  have havg : (univ : Finset (P → Bool)).card •
      ((A.card : ℝ)/Fintype.card (P → Bool)) ≤ A.card := by
    simp only [card_univ, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk.ne']
  obtain ⟨c, _, hc⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf ht havg
  let B := A.filter (fun a => f a = c)
  have hcardR : (A.card : ℝ) ≤ Fintype.card (P → Bool)*B.card := by
    have hh := (div_le_iff₀ hk).mp hc
    simpa only [mul_comm] using hh
  have hcard : A.card ≤ 2^P.card*B.card := by
    have hcnt : Fintype.card (P → Bool)=2^P.card := by simp
    rw [hcnt] at hcardR
    exact_mod_cast hcardR
  refine ⟨B, filter_subset _ _, hcard, ?_⟩
  intro a ha b hb p hp
  obtain ⟨haA, hac⟩ := mem_filter.mp ha
  obtain ⟨_, hbc⟩ := mem_filter.mp hb
  apply localColor_avoids (hP p hp).1 (hP p hp).2
    (hunit a haA p hp)
  exact congrFun (hac.trans hbc.symm) ⟨p,hp⟩

/-- The extraction applied to prime roots. Only primes in P themselves
need to be deleted to meet all unit hypotheses. -/
theorem prime_extraction (n : ℕ) (hn : 128 ≤ n) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    ∃ B ⊆ sievePrimes n,
      (n : ℝ)/8 ≤ ((2^P.card : ℕ)*B.card + P.card : ℕ)*Real.log n ∧
      ∀ a ∈ B, ∀ b ∈ B, ∀ p ∈ P, ¬p ∣ a^2+b^2 := by
  have hunit : ∀ a ∈ sievePrimes n \ P, ∀ p ∈ P, ¬p ∣ a := by
    intro a ha p hp hd
    obtain ⟨haA,haP⟩ := mem_sdiff.mp ha
    have hprime := (mem_filter.mp haA).2.1
    have he : a=p := (hprime.dvd_iff_eq (hP p hp).1.ne_one).mp hd
    exact haP (he ▸ hp)
  obtain ⟨B,hB,hc,hr⟩ := finite_extraction (sievePrimes n \ P) P hP hunit
  have hc' : (sievePrimes n).card ≤ 2^P.card*B.card+P.card :=
    card_le_card_sdiff_add_card.trans (Nat.add_le_add_right hc _)
  refine ⟨B,hB.trans sdiff_subset,?_,hr⟩
  apply (sievePrimes_card_log_lower n hn).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc')
    (Real.log_nonneg (by exact_mod_cast (show 1≤n by omega)))

private lemma color_cost {X δ : ℝ} {k : ℕ} (hX : 1≤X)
    (hk : (k:ℝ)≤δ/4*Real.log X) : (2:ℝ)^k≤X^(δ/4) := by
  have hX0 : 0<X := by linarith
  have hlog2 : Real.log 2≤1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this
    exact this
  rw [Real.rpow_def_of_pos hX0]
  calc
    (2:ℝ)^k = Real.exp ((k:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
    _ ≤ Real.exp (Real.log X*(δ/4)) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k : (0:ℝ)≤k)
      nlinarith only [hh,hk]

/-- Uniform near-linear prime carriers for any prescribed collection of
at most `(δ/4) log n` odd primes. This concludes only roughness, not Sidonness. -/
theorem eventually_prime_carrier (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2<p) → (P.card:ℝ)≤δ/4*Real.log n →
      ∃ B ⊆ sievePrimes n, (n:ℝ)^(1-δ)≤B.card ∧
        ∀ a ∈ B, ∀ b ∈ B, ∀ p ∈ P, ¬p ∣ a^2+b^2 := by
  have hsmall := ((isLittleO_log_rpow_atTop (by linarith : 0<δ/4)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n:ℝ))
      Filter.atTop Filter.atTop)).bound (by norm_num : (0:ℝ)<1/32)
  filter_upwards [hsmall, Filter.eventually_ge_atTop 128] with n hs hn
  have hX : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hX0 : (0:ℝ)<n := by linarith
  have hL : 0≤Real.log (n:ℝ) := Real.log_nonneg hX
  have hs' : Real.log (n:ℝ)≤(n:ℝ)^(δ/4)/32 := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL,
      abs_of_nonneg (Real.rpow_nonneg hX0.le _),one_div_mul_eq_div] using hs
  intro P hP hcost
  obtain ⟨B,hB,hcard,hr⟩ := prime_extraction n hn P hP
  refine ⟨B,hB,?_,hr⟩
  by_contra hb
  have hb' : (B.card:ℝ)≤(n:ℝ)^(1-δ) := (lt_of_not_ge hb).le
  have hk := color_cost hX hcost
  have hkL : (P.card:ℝ)≤Real.log (n:ℝ) := by nlinarith only [hcost,hL,hδ1]
  have hlead : (2:ℝ)^P.card*B.card≤(n:ℝ)^(1-3*δ/4) := by
    calc
      _ ≤ (n:ℝ)^(δ/4)*(n:ℝ)^(1-δ) :=
        mul_le_mul hk hb' (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _)
      _ = _ := by rw [←Real.rpow_add hX0]; congr 1; ring
  push_cast at hcard
  have hbound : ((2:ℝ)^P.card*B.card+P.card)*Real.log (n:ℝ)≤(n:ℝ)/16 := by
    calc
      _ ≤ ((n:ℝ)^(1-3*δ/4)+(n:ℝ)^(δ/4)/32)*((n:ℝ)^(δ/4)/32) :=
        mul_le_mul (add_le_add hlead (hkL.trans hs')) hs' hL (by positivity)
      _ ≤ ((n:ℝ)^(1-3*δ/4)+(n:ℝ)^(δ/4))*((n:ℝ)^(δ/4)/32) := by
        gcongr
        have hh := Real.rpow_nonneg hX0.le (δ/4)
        linarith only [hh]
      _ = ((n:ℝ)^(1-δ/2)+(n:ℝ)^(δ/2))/32 := by
        rw [add_mul, ←mul_div_assoc, ←mul_div_assoc, ←Real.rpow_add hX0,
          ←Real.rpow_add hX0]
        have e1 : 1-3*δ/4+δ/4=1-δ/2 := by ring
        have e2 : δ/4+δ/4=δ/2 := by ring
        rw [e1,e2]
        ring
      _ ≤ ((n:ℝ)+(n:ℝ))/32 := by
        gcongr
        · calc
            (n:ℝ)^(1-δ/2)≤(n:ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX (by linarith)
            _ = n := Real.rpow_one _
        · calc
            (n:ℝ)^(δ/2)≤(n:ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX (by linarith)
            _ = n := Real.rpow_one _
      _ = _ := by ring
  linarith only [hcard,hbound,hX0]

/-- Excluding arbitrarily many specified odd prime factors does not by
itself imply Sidonness. The collision height is quadratic in their product. -/
theorem rough_collision (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    ∃ a b c d : ℕ, 0<a ∧ a<d ∧ d<c ∧ c<b ∧
      b≤10*(∏ p ∈ P, p)^2+7*(∏ p ∈ P, p)+1 ∧
      a^2+b^2=c^2+d^2 ∧
      ∀ x ∈ ({a,b,c,d} : Finset ℕ), ∀ y ∈ ({a,b,c,d} : Finset ℕ),
        ∀ p ∈ P, ¬p ∣ x^2+y^2 := by
  let Q := ∏ p ∈ P, p
  have hQ : 0<Q := prod_pos (fun p hp => (hP p hp).1.pos)
  obtain ⟨a,b,c,d,ha,hb,_,_,har,hbr,hcr,hdr,had,hdc,hcb,he⟩ :=
    PrimeResidueRotation.quadratic_height_collision hQ
  refine ⟨a,b,c,d,(mem_Icc.mp ha).1,had,hdc,hcb,(mem_Icc.mp hb).2,he,?_⟩
  have hres : ∀ x ∈ ({a,b,c,d} : Finset ℕ), x ≡ 1 [MOD Q] := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  intro x hx y hy p hp hd
  have hpQ : p ∣ Q := dvd_prod_of_mem (fun p : ℕ => p) hp
  have hm := ((hres x hx).pow 2).add ((hres y hy).pow 2)
  have ht : p ∣ 2 := by simpa using (hm.dvd_iff hpQ).mp hd
  exact (not_le_of_gt (hP p hp).2) (Nat.le_of_dvd (by decide) ht)


/-- An explicit logarithmic-cutoff obstruction, with no primality claim
for the roots: four distinct positive roots below 18*16^k collide despite
all their pairwise norms avoiding every odd prime up to k. -/
theorem logarithmic_rough_collision (k : ℕ) :
    ∃ a b c d : ℕ, 0<a ∧ a<d ∧ d<c ∧ c<b ∧ b≤18*16^k ∧
      a^2+b^2=c^2+d^2 ∧
      ∀ x∈({a,b,c,d} : Finset ℕ), ∀ y∈({a,b,c,d} : Finset ℕ),
        ∀ p : ℕ, p.Prime → 2<p → p≤k → ¬p ∣ x^2+y^2 := by
  let P := (range (k+1)).filter (fun p => p.Prime ∧ 2<p)
  have hP : ∀ p∈P, p.Prime ∧ 2<p := fun _ hp => (mem_filter.mp hp).2
  let Q := ∏ p∈P, p
  have hQ : Q≤4^k := by
    apply le_trans (b:=primorial k) _ (primorial_le_4_pow k)
    apply prod_le_prod_of_subset_of_one_le'
    · intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(hP p hp).1⟩
    · intro p hp _
      exact (mem_filter.mp hp).2.one_lt.le
  obtain ⟨a,b,c,d,ha,had,hdc,hcb,hheight,he,hr⟩ := rough_collision P hP
  refine ⟨a,b,c,d,ha,had,hdc,hcb,?_,he,?_⟩
  · have hU : 1≤(4:ℕ)^k := by
      have hh : 0<(4:ℕ)^k := by positivity
      omega
    have hs := Nat.pow_le_pow_left hQ 2
    have hUU : (4:ℕ)^k≤((4:ℕ)^k)^2 := by nlinarith only [hU]
    have hsq : ((4:ℕ)^k)^2=(16:ℕ)^k := by
      rw [←pow_mul, Nat.mul_comm k 2,pow_mul]
      norm_num
    change b≤10*Q^2+7*Q+1 at hheight
    rw [←hsq]
    nlinarith only [hheight,hQ,hs,hU,hUU]
  · intro x hx y hy p hp hp2 hpk
    exact hr x hx y hy p (mem_filter.mpr ⟨mem_range.mpr (by omega),hp,hp2⟩)


end Erdos773.RoughPairNorms
#print axioms Erdos773.RoughPairNorms.localColor_avoids
#print axioms Erdos773.RoughPairNorms.finite_extraction

#print axioms Erdos773.RoughPairNorms.prime_extraction
#print axioms Erdos773.RoughPairNorms.rough_collision

#print axioms Erdos773.RoughPairNorms.eventually_prime_carrier

#print axioms Erdos773.RoughPairNorms.logarithmic_rough_collision
