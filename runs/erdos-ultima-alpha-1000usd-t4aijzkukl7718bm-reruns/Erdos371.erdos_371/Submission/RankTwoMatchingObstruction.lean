import FormalConjecturesUtil

/-! Two bad inputs with two distinct prime factors above the slope still
cannot be matched using only their largest input prime. This finite obstruction
neither refutes an aggregate deficit bound nor disproves Erdős 371. -/

namespace Erdos371RankTwoMatchingObstruction

open Finset
abbrev P := Nat.maxPrimeFac

def sources : Finset ℕ := {15117,25195}
def roots : Finset ℕ := {2520,7559,12598,17637,22676}

lemma top_product {a q : ℕ} (ha : 0<a) (hq : q.Prime) (h : P a≤q) : P (a*q)=q := by
  rw [P, Nat.maxPrimeFac_mul ha.ne' hq.ne_zero, hq.maxPrimeFac_eq_self]
  exact max_eq_right h

@[simp] lemma top_5039 : P 5039=5039 := by
  exact (show Nat.Prime 5039 by norm_num).maxPrimeFac_eq_self
@[simp] lemma top_15117 : P 15117=5039 := by
  change P (3*5039)=5039
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_25195 : P 25195=5039 := by
  change P (5*5039)=5039
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_30233 : P 30233=617 := by
  change P (49*617)=617
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_50389 : P 50389=1229 := by
  change P (41*1229)=1229
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_2520 : P 2520=7 := by
  change P (360*7)=7
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_7559 : P 7559=7559 := by
  exact (show Nat.Prime 7559 by norm_num).maxPrimeFac_eq_self
@[simp] lemma top_12598 : P 12598=6299 := by
  change P (2*6299)=6299
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_17637 : P 17637=5879 := by
  change P (3*5879)=5879
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_22676 : P 22676=5669 := by
  change P (4*5669)=5669
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_35273 : P 35273=5039 := by
  change P (7*5039)=5039
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)
@[simp] lemma top_45351 : P 45351=5039 := by
  change P (9*5039)=5039
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

lemma source_properties : ∀ a∈sources,
    a∈Icc 1 25195 ∧ ¬a.Prime ∧ ¬2∣a ∧ P a=5039 ∧ P (2*a-1)<P a := by
  intro a ha
  simp only [sources, mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl <;> norm_num

lemma source_two_large_factors : ∀ a∈sources,
    2≤(a.primeFactors.filter (fun r => 2<r)).card := by
  have hq : Nat.Prime 5039 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  intro a ha
  simp only [sources, mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl
  · change 2≤((3*5039).primeFactors.filter (fun r => 2<r)).card
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num), h3.primeFactors, hq.primeFactors]
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  · change 2≤((5*5039).primeFactors.filter (fun r => 2<r)).card
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num), h5.primeFactors, hq.primeFactors]
    norm_num [Finset.filter_insert, Finset.filter_singleton]

set_option maxHeartbeats 4000000 in
lemma root_bound {b : ℕ} (hb : b∈Icc 1 25195) (hd : 5039∣2*b-1) : b∈roots := by
  obtain ⟨hb1,hbA⟩ := mem_Icc.mp hb
  obtain ⟨k,hk⟩ := hd
  have he : 2*b=5039*k+1 := by omega
  have hkmod : k%2=1 := by omega
  have hkd : k=2*(k/2)+1 := by omega
  have hbe : b=2520+5039*(k/2) := by omega
  have hj : k/2≤4 := by omega
  simp only [roots, mem_insert, mem_singleton]
  interval_cases h : k/2 <;> omega

lemma favorable_roots : roots.filter (fun b => P b≤P (2*b-1))={2520} := by
  norm_num [roots, Finset.filter_insert, Finset.filter_singleton]

lemma unique_target {b : ℕ} (hb : b∈Icc 1 25195) (hd : 5039∣2*b-1)
    (hgood : P b≤P (2*b-1)) : b=2520 := by
  have hm : b∈roots.filter (fun b => P b≤P (2*b-1)) :=
    mem_filter.mpr ⟨root_bound hb hd,hgood⟩
  simpa only [favorable_roots,mem_singleton] using hm

/-- The two-prime restriction does not repair this largest-prime graph. -/
theorem no_largest_prime_matching :
    ¬ ∃ f : sources → ℕ, Function.Injective f ∧ ∀ a : sources,
      f a∈Icc 1 25195 ∧ P a∣2*f a-1 ∧ P (f a)≤P (2*f a-1) := by
  rintro ⟨f,hf,hmem⟩
  let a : sources := ⟨15117,by simp [sources]⟩
  let b : sources := ⟨25195,by simp [sources]⟩
  have ha := hmem a
  have hb := hmem b
  have hqa : P (a:ℕ)=5039 := top_15117
  have hqb : P (b:ℕ)=5039 := top_25195
  have hea := unique_target ha.1 (by simpa only [hqa] using ha.2.1) ha.2.2
  have heb := unique_target hb.1 (by simpa only [hqb] using hb.2.1) hb.2.2
  have he := congrArg Subtype.val (hf (hea.trans heb.symm))
  norm_num [a,b] at he

end Erdos371RankTwoMatchingObstruction

#print axioms Erdos371RankTwoMatchingObstruction.source_two_large_factors
#print axioms Erdos371RankTwoMatchingObstruction.no_largest_prime_matching
