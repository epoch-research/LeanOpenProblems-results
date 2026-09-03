import FormalConjecturesUtil

/-! The largest-input-prime matching still fails after discarding prime inputs
and inputs divisible by the slope. This does not refute a matching using every
input prime factor, any affine prefix bound, or Erdős 371. -/

namespace Erdos371DiscardedMatchingObstruction

open Finset
abbrev P := Nat.maxPrimeFac

def S : Finset ℕ := {5926,11852,14815,20741,23704,29630}
def T : Finset ℕ := {988,3951,9877,12840,18766}
def roots : Finset ℕ := {988,3951,6914,9877,12840,15803,18766,21729,24692,27655}

lemma top_product {a q : ℕ} (ha : 0 < a) (hq : q.Prime) (h : P a ≤ q) : P (a*q) = q := by
  rw [P, Nat.maxPrimeFac_mul ha.ne' hq.ne_zero, hq.maxPrimeFac_eq_self]
  exact max_eq_right h

@[simp] lemma top_988 : P 988 = 19 := by
  change P (52*19) = 19
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_2963 : P 2963 = 2963 := by
  change P (1*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_3951 : P 3951 = 439 := by
  change P (9*439) = 439
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_5926 : P 5926 = 2963 := by
  change P (2*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_6914 : P 6914 = 3457 := by
  change P (2*3457) = 3457
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_9877 : P 9877 = 83 := by
  change P (119*83) = 83
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_11852 : P 11852 = 2963 := by
  change P (4*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_12840 : P 12840 = 107 := by
  change P (120*107) = 107
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_14815 : P 14815 = 2963 := by
  change P (5*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_15803 : P 15803 = 15803 := by
  change P (1*15803) = 15803
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_17777 : P 17777 = 613 := by
  change P (29*613) = 613
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_18766 : P 18766 = 853 := by
  change P (22*853) = 853
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_20741 : P 20741 = 2963 := by
  change P (7*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_21729 : P 21729 = 7243 := by
  change P (3*7243) = 7243
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_23704 : P 23704 = 2963 := by
  change P (8*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_24692 : P 24692 = 6173 := by
  change P (4*6173) = 6173
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_27655 : P 27655 = 5531 := by
  change P (5*5531) = 5531
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_29630 : P 29630 = 2963 := by
  change P (10*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_35555 : P 35555 = 547 := by
  change P (65*547) = 547
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_38519 : P 38519 = 2963 := by
  change P (13*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_44444 : P 44444 = 271 := by
  change P (164*271) = 271
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_47408 : P 47408 = 2963 := by
  change P (16*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_56297 : P 56297 = 2963 := by
  change P (19*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_62222 : P 62222 = 587 := by
  change P (106*587) = 587
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_65186 : P 65186 = 2963 := by
  change P (22*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_71111 : P 71111 = 89 := by
  change P (799*89) = 89
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_74075 : P 74075 = 2963 := by
  change P (25*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_82964 : P 82964 = 2963 := by
  change P (28*2963) = 2963
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

@[simp] lemma top_88889 : P 88889 = 863 := by
  change P (103*863) = 863
  exact top_product (by norm_num) (by norm_num) (by decide +kernel)

lemma source_properties : ∀ a ∈ S,
    a ∈ Icc 1 30000 ∧ ¬a.Prime ∧ ¬3 ∣ a ∧ P a = 2963 ∧ P (3*a-1) < P a := by
  intro a ha
  simp only [S, mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

set_option maxHeartbeats 4000000 in
lemma root_bound {b : ℕ} (hb : b ∈ Icc 1 30000) (hd : 2963 ∣ 3*b-1) :
    b ∈ roots := by
  obtain ⟨hb1, hbA⟩ := mem_Icc.mp hb
  obtain ⟨k, hk⟩ := hd
  have hpos : 1 ≤ 3*b := by omega
  have he : 3*b = 2963*k+1 := by omega
  have hkmod : k % 3 = 1 := by omega
  have hkdiv : k = 3*(k/3)+1 := by omega
  have hbe : b = 988+2963*(k/3) := by omega
  have hj : k/3 ≤ 9 := by omega
  simp only [roots, mem_insert, mem_singleton]
  interval_cases h : k/3 <;> omega

lemma favorable_roots : roots.filter (fun b => P b ≤ P (3*b-1)) = T := by
  norm_num [roots, T, Finset.filter_insert, Finset.filter_singleton]

lemma target_mem {b : ℕ} (hb : b ∈ Icc 1 30000) (hd : 2963 ∣ 3*b-1)
    (hgood : P b ≤ P (3*b-1)) : b ∈ T := by
  rw [← favorable_roots]
  exact mem_filter.mpr ⟨root_bound hb hd, hgood⟩

/-- These six retained sources cannot be matched injectively to favorable
inputs whose affine values share the sources' largest input prime. -/
theorem no_largest_prime_matching_after_discards :
    ¬ ∃ f : S → ℕ, Function.Injective f ∧ ∀ a : S,
      f a ∈ Icc 1 30000 ∧ P a ∣ 3*f a-1 ∧ P (f a) ≤ P (3*f a-1) := by
  rintro ⟨f, hf, hmem⟩
  have hT (a : S) : f a ∈ T := by
    obtain ⟨hb, hd, hgood⟩ := hmem a
    have he := (source_properties a a.property).2.2.2.1
    rw [he] at hd
    exact target_mem hb hd hgood
  let g : S → T := fun a => ⟨f a, hT a⟩
  have hg : Function.Injective g := by
    intro a b he
    exact hf (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective g hg
  have hS : S.card = 6 := by decide +kernel
  have hT' : T.card = 5 := by decide +kernel
  simp only [Fintype.card_coe, hS, hT'] at hc
  omega

end Erdos371DiscardedMatchingObstruction

#print axioms Erdos371DiscardedMatchingObstruction.source_properties
#print axioms Erdos371DiscardedMatchingObstruction.no_largest_prime_matching_after_discards
