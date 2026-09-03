import FormalConjecturesUtil
import Submission.FavorableTargetFamilies

/-! Favorable targets eventually outnumber affine sources with any fixed finite
prime support. The threshold depends on that support. This is not a uniform
Hall inequality and does not prove Erdős 371. -/

namespace Erdos371FixedSupportFavorableCount

open Finset Filter Erdos371FavorableTargetFamilies

/-- The elementary exponent-vector bound for a finite prime support. -/
lemma support_count {T R : Finset ℕ} {f : ℕ → ℕ} {H : ℕ}
    (hf : Set.InjOn f (T : Set ℕ))
    (hpos : ∀ a ∈ T, f a ≠ 0)
    (hsize : ∀ a ∈ T, f a ≤ 2^H)
    (hR : ∀ a ∈ T, (f a).primeFactors ⊆ R) :
    T.card ≤ (H+1)^R.card := by
  classical
  have he (a : T) (r : R) : (f a).factorization r ≤ H := by
    by_cases hr : (r : ℕ).Prime
    · exact Nat.factorization_le_of_le_pow
        ((hsize a a.property).trans (Nat.pow_le_pow_left hr.two_le H))
    · rw [Nat.factorization_eq_zero_of_not_prime _ hr]
      omega
  let F : T → (R → Fin (H+1)) := fun a r =>
    ⟨(f a).factorization r, Nat.lt_succ_of_le (he a r)⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply hf a.property b.property
    apply Nat.factorization_inj (hpos a a.property) (hpos b b.property)
    apply Finsupp.ext
    intro r
    by_cases hr : r ∈ R
    · exact congrArg Fin.val (congrFun hab ⟨r, hr⟩)
    · have ha : (f a).factorization r = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [Nat.support_factorization]
        exact fun h => hr (hR a a.property h)
      have hb : (f b).factorization r = 0 := by
        apply Finsupp.notMem_support_iff.mp
        rw [Nat.support_factorization]
        exact fun h => hr (hR b b.property h)
      rw [ha, hb]
  simpa using Fintype.card_le_of_injective F hF

lemma plus_family_arbitrary_dimension {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (K : ℕ) :
    ∃ b C : ℕ, 0 < b ∧ 2 ≤ C ∧ ∀ L : ℕ,
      (L+1)^K ≤ ((Icc 1 (b*C^L)).filter
        (fun a => r ∣ p*a+1 ∧ P a < P (p*a+1))).card := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (Nat.infinite_setOf_prime.diff (Set.finite_singleton r)).exists_subset_card_eq K
  have hprime (i : s) : (i : ℕ).Prime := (hs i.property).1
  have hne (i : s) : (i : ℕ) ≠ r := (hs i.property).2
  obtain ⟨b, C, hb, hC, hfamily⟩ := plus_family hprime Subtype.val_injective hp hr hrp hne
  refine ⟨b, C+1, hb, by omega, ?_⟩
  intro L
  have hsub : (Icc 1 (b*C^L)).filter (fun a => r ∣ p*a+1 ∧ P a < P (p*a+1)) ⊆
      (Icc 1 (b*(C+1)^L)).filter (fun a => r ∣ p*a+1 ∧ P a < P (p*a+1)) := by
    intro a ha
    obtain ⟨ha, hgood⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,
      (mem_Icc.mp ha).2.trans (Nat.mul_le_mul_left b (Nat.pow_le_pow_left (by omega) L))⟩,
      hgood⟩
  simpa only [Fintype.card_coe, hcard] using (hfamily L).trans (Finset.card_le_card hsub)

lemma minus_family_arbitrary_dimension {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (K : ℕ) :
    ∃ b C : ℕ, 0 < b ∧ 2 ≤ C ∧ ∀ L : ℕ,
      (L+1)^K ≤ ((Icc 1 (b*C^L)).filter
        (fun a => r ∣ p*a-1 ∧ P a < P (p*a-1))).card := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    (Nat.infinite_setOf_prime.diff (Set.finite_singleton r)).exists_subset_card_eq K
  have hprime (i : s) : (i : ℕ).Prime := (hs i.property).1
  have hne (i : s) : (i : ℕ) ≠ r := (hs i.property).2
  obtain ⟨b, C, hb, hC, hfamily⟩ := minus_family hprime Subtype.val_injective hp hr hrp hne
  refine ⟨b, C+1, hb, by omega, ?_⟩
  intro L
  have hsub : (Icc 1 (b*C^L)).filter (fun a => r ∣ p*a-1 ∧ P a < P (p*a-1)) ⊆
      (Icc 1 (b*(C+1)^L)).filter (fun a => r ∣ p*a-1 ∧ P a < P (p*a-1)) := by
    intro a ha
    obtain ⟨ha, hgood⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1,
      (mem_Icc.mp ha).2.trans (Nat.mul_le_mul_left b (Nat.pow_le_pow_left (by omega) L))⟩,
      hgood⟩
  simpa only [Fintype.card_coe, hcard] using (hfamily L).trans (Finset.card_le_card hsub)

lemma affine_exp_bound (p b C L : ℕ) :
    p*(b*C^(L+1))+1 ≤ 2^((p+b+C+1)*(L+1)) := by
  have hprod : p*(b*C^(L+1)) ≤ 2^(p+b+C*(L+1)) := by
    calc
      _ ≤ 2^p*(2^b*(2^C)^(L+1)) :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.mul_le_mul Nat.lt_two_pow_self.le
          (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _))
      _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
  have hpow : 1 ≤ 2^(p+b+C*(L+1)) := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 2^(p+b+C*(L+1)) * 2 := by omega
    _ = 2^(p+b+C*(L+1)+1) := by rw [pow_succ]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- A general comparison between polynomial-in-logarithm source counts and a
multiplicative family of targets. The threshold is allowed to depend on `R`. -/
lemma eventually_support_le_family {p : ℕ} (R : Finset ℕ) {f : ℕ → ℕ} {G : ℕ → Prop} [DecidablePred G]
    (hf : Set.InjOn f (Set.Ici 1))
    (hpos : ∀ a, 1 ≤ a → f a ≠ 0)
    (hfsize : ∀ a, f a ≤ p*a+1)
    (hfamily : ∃ b C : ℕ, 0 < b ∧ 2 ≤ C ∧ ∀ L : ℕ,
      (L+1)^(R.card+1) ≤ ((Icc 1 (b*C^L)).filter G).card) :
    ∀ᶠ A : ℕ in atTop,
      ((Icc 1 A).filter (fun a => (f a).primeFactors ⊆ R)).card ≤
        ((Icc 1 A).filter G).card := by
  classical
  obtain ⟨b, C, hb, hC, hfamily⟩ := hfamily
  let D := p+b+C+1
  let T := (D+1)^R.card
  apply Filter.eventually_atTop.mpr
  refine ⟨b*C^T, ?_⟩
  intro A hA
  have hdiv : C^T ≤ A/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa [mul_comm] using hA)
  have hAb : A/b ≠ 0 := by
    have hpow : 0 < C^T := pow_pos (by omega) _
    omega
  let L := Nat.log C (A/b)
  have hTL : T ≤ L := Nat.le_log_of_pow_le (by omega) hdiv
  have hlo : b*C^L ≤ A := by
    have hh := Nat.pow_log_le_self C hAb
    have hm := (Nat.le_div_iff_mul_le hb).mp hh
    simpa only [L, mul_comm] using hm
  have hhi : A < b*C^(L+1) := by
    have hh := Nat.lt_pow_succ_log_self (by omega : 1 < C) (A/b)
    have hm := (Nat.div_lt_iff_lt_mul hb).mp hh
    simpa only [L, Nat.succ_eq_add_one, mul_comm] using hm
  have hsource : ((Icc 1 A).filter (fun a => (f a).primeFactors ⊆ R)).card ≤
      (D*(L+1)+1)^R.card := by
    apply support_count (f := f) (R := R) (H := D*(L+1))
    · intro a ha b hb he
      have ha1 : 1 ≤ a := (mem_Icc.mp (mem_filter.mp ha).1).1
      have hb1 : 1 ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
      exact hf ha1 hb1 he
    · intro a ha
      exact hpos a (mem_Icc.mp (mem_filter.mp ha).1).1
    · intro a ha
      have haA := (mem_Icc.mp (mem_filter.mp ha).1).2
      calc
        f a ≤ p*a+1 := hfsize a
        _ ≤ p*(b*C^(L+1))+1 := Nat.add_le_add_right (Nat.mul_le_mul_left p (haA.trans hhi.le)) 1
        _ ≤ 2^(D*(L+1)) := affine_exp_bound p b C L
    · intro a ha
      exact (mem_filter.mp ha).2
  have hpoly : (D*(L+1)+1)^R.card ≤ (L+1)^(R.card+1) := by
    calc
      _ ≤ ((D+1)*(L+1))^R.card := Nat.pow_le_pow_left (by nlinarith) _
      _ = (D+1)^R.card*(L+1)^R.card := mul_pow _ _ _
      _ ≤ (L+1)*(L+1)^R.card := Nat.mul_le_mul_right _ (by dsimp [T] at hTL; omega)
      _ = _ := by rw [pow_succ]; ring
  have htarget : ((Icc 1 (b*C^L)).filter G).card ≤ ((Icc 1 A).filter G).card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨ha, hG⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha).1, (mem_Icc.mp ha).2.trans hlo⟩, hG⟩
  exact hsource.trans (hpoly.trans ((hfamily L).trans htarget))

/-- For any fixed support `R` and prime `r` coprime to the slope, favorable
plus targets sharing `r` eventually outnumber *all* sources with support `R`.
This has no uniformity as `R` grows. -/
theorem plus_fixed_support {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (R : Finset ℕ) :
    ∀ᶠ A : ℕ in atTop,
      ((Icc 1 A).filter (fun a => (p*a+1).primeFactors ⊆ R)).card ≤
        ((Icc 1 A).filter (fun a => r ∣ p*a+1 ∧ P a < P (p*a+1))).card := by
  apply eventually_support_le_family (p := p) R
  · intro a _ b _ h
    change p*a+1 = p*b+1 at h
    have hh : p*a = p*b := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hh
  · intro a ha
    omega
  · intro a
    exact le_rfl
  · exact plus_family_arbitrary_dimension hp hr hrp (R.card+1)

/-- The same fixed-support statement for minus comparisons. -/
theorem minus_fixed_support {p r : ℕ} (hp : 2 ≤ p) (hr : r.Prime)
    (hrp : r.Coprime p) (R : Finset ℕ) :
    ∀ᶠ A : ℕ in atTop,
      ((Icc 1 A).filter (fun a => (p*a-1).primeFactors ⊆ R)).card ≤
        ((Icc 1 A).filter (fun a => r ∣ p*a-1 ∧ P a < P (p*a-1))).card := by
  apply eventually_support_le_family (p := p) R
  · intro a ha b hb h
    change p*a-1 = p*b-1 at h
    have ha' : 1 ≤ a := ha
    have hb' : 1 ≤ b := hb
    have hpa : 2 ≤ p*a := by nlinarith
    have hpb : 2 ≤ p*b := by nlinarith
    have hh : p*a = p*b := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) hh
  · intro a ha
    have hpa : 2 ≤ p*a := by nlinarith
    omega
  · intro a
    omega
  · exact minus_family_arbitrary_dimension hp hr hrp (R.card+1)

end Erdos371FixedSupportFavorableCount

#print axioms Erdos371FixedSupportFavorableCount.support_count
#print axioms Erdos371FixedSupportFavorableCount.plus_fixed_support
#print axioms Erdos371FixedSupportFavorableCount.minus_fixed_support
