import FormalConjecturesUtil
import Submission.DiscardedMatchingCriterion

/-! A finite obstruction to restricting an affine matching edge to the
largest prime of the target's affine value. This is NOT a disproof of
Erdős 371 or of the all-input/all-target-prime matching criterion. -/

namespace Erdos371TargetMaxMatchingObstruction

open Finset Erdos371DiscardedMatchingCriterion

abbrev slope : ℕ := 5
abbrev cutoff : ℕ := 40676
abbrev affine (a : ℕ) : ℕ := 5*a-1

def sources : Finset ℕ :=
  {9946,14919,19498,19892,20338,29247,29838,30507,38996,39784,40676}

def support : Finset ℕ := {2,3,4973,9749,10169}

def targets : Finset ℕ := {1,2,1950,2034,2984,7957,12930,21448,22372,22876}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma sources_retained : ∀ a ∈ sources, a ∈ retained slope cutoff affine := by
  intro a ha
  simp only [sources,mem_insert,mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [retained,mem_filter,mem_Icc,P,affine,slope,cutoff]
    norm_num
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma sources_supported : ∀ a ∈ sources, a.primeFactors ⊆ support := by
  decide +kernel

def smallCandidates : Finset ℕ :=
  ((range 17).product (range 17)).image fun uv => 2^uv.1*3^uv.2

def rootCandidates (q : ℕ) : Finset ℕ :=
  (range 41).image fun m => (q*m+1)/5

def candidates : Finset ℕ :=
  smallCandidates ∪ rootCandidates 4973 ∪ rootCandidates 9749 ∪ rootCandidates 10169

def eligible (b : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ cutoff ∧ Nat.maxPrimeFac b ≤ Nat.maxPrimeFac (affine b) ∧
    Nat.maxPrimeFac (affine b) ∈ support

instance (b : ℕ) : Decidable (eligible b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

lemma small_mem {b : ℕ} (hb : 1 ≤ b) (hbA : b ≤ cutoff)
    (hP : Nat.maxPrimeFac b ≤ 3) : b ∈ smallCandidates := by
  have hs : b.factorization.support ⊆ ({2,3} : Finset ℕ) := by
    intro q hq
    rw [Nat.support_factorization] at hq
    obtain ⟨hqP,hqd,hb0⟩ := Nat.mem_primeFactors.mp hq
    have hq2 := hqP.two_le
    have hq3 := (Nat.le_maxPrimeFac hb0 hqP hqd).trans hP
    simp only [mem_insert,mem_singleton]
    omega
  have he := Finsupp.prod_of_support_subset b.factorization hs
    (fun q k : ℕ => q^k) (by simp)
  rw [Nat.factorization_prod_pow_eq_self (by omega)] at he
  simp only [prod_insert,prod_singleton,show (2:ℕ) ≠ 3 by omega,
    mem_singleton,not_false_eq_true] at he
  have h2 : b.factorization 2 ≤ 16 := Nat.factorization_le_of_le_pow (by
    change b ≤ 65536
    exact hbA.trans (by norm_num [cutoff]))
  have h3 : b.factorization 3 ≤ 16 := Nat.factorization_le_of_le_pow (by
    change b ≤ 43046721
    exact hbA.trans (by norm_num [cutoff]))
  apply mem_image.mpr
  exact ⟨(b.factorization 2,b.factorization 3),
    mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,he.symm⟩

lemma root_mem {b q : ℕ} (hb : 1 ≤ b) (hbA : b ≤ cutoff)
    (hq : 4973 ≤ q) (hd : q ∣ affine b) : b ∈ rootCandidates q := by
  let m := affine b / q
  have hm : m*q = affine b := Nat.div_mul_cancel hd
  have haff : affine b + 1 = 5*b := by dsimp [affine]; omega
  have hm40 : m < 41 := by
    have hqm := Nat.mul_le_mul_left m hq
    dsimp [cutoff] at hbA
    nlinarith
  apply mem_image.mpr
  refine ⟨m,mem_range.mpr hm40,?_⟩
  have he : q*m+1 = 5*b := by nlinarith
  rw [he,Nat.mul_div_right _ (by norm_num : 0 < (5:ℕ))]

lemma eligible_mem {b : ℕ} (hb : eligible b) : b ∈ candidates := by
  obtain ⟨hb1,hbA,hP,hq⟩ := hb
  have hd : Nat.maxPrimeFac (affine b) ∣ affine b := Nat.maxPrimeFac_dvd
  simp only [support,mem_insert,mem_singleton] at hq
  rcases hq with hq | hq | hq | hq | hq
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _
      (small_mem hb1 hbA (by omega))))
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _
      (small_mem hb1 hbA (by omega))))
  · rw [hq] at hd
    exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (root_mem hb1 hbA (by omega) hd)))
  · rw [hq] at hd
    exact mem_union_left _ (mem_union_right _ (root_mem hb1 hbA (by omega) hd))
  · rw [hq] at hd
    exact mem_union_right _ (root_mem hb1 hbA (by omega) hd)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma checked_candidates : candidates.filter eligible = targets := by
  decide +kernel

lemma targets_eq :
    ((favorable cutoff affine).filter fun b => Nat.maxPrimeFac (affine b) ∈ support) = targets := by
  rw [← checked_candidates]
  ext b
  simp only [mem_filter,favorable,mem_Icc,eligible]
  constructor
  · rintro ⟨⟨hb,hP⟩,hs⟩
    exact ⟨eligible_mem ⟨hb.1,hb.2,hP,hs⟩,hb.1,hb.2,hP,hs⟩
  · rintro ⟨_,hb,hbA,hP,hs⟩
    exact ⟨⟨⟨hb,hbA⟩,hP⟩,hs⟩

lemma source_card : sources.card = 11 := by decide +kernel
lemma target_card : targets.card = 10 := by decide +kernel

lemma target_mem {a b : ℕ} (ha : a ∈ sources)
    (hb : b ∈ favorable cutoff affine) (hedge : Nat.maxPrimeFac (affine b) ∣ a) :
    b ∈ targets := by
  have hb1 : 1 ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
  have hab : 1 < affine b := by dsimp [affine]; omega
  have hprime := Nat.prime_maxPrimeFac_of_one_lt (affine b) hab
  have ha0 : a ≠ 0 := by
    have har := sources_retained a ha
    have ha1 := (mem_Icc.mp (mem_filter.mp har).1).1
    omega
  rw [← targets_eq]
  exact mem_filter.mpr ⟨hb, sources_supported a ha (Nat.mem_primeFactors.mpr
    ⟨hprime, hedge, ha0⟩)⟩

/-- Eleven retained sources have only ten neighbors when each edge is
required to use the target's largest prime. -/
theorem no_target_max_matching :
    ¬ ∃ f : sources → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ favorable cutoff affine ∧ Nat.maxPrimeFac (affine (f a)) ∣ (a : ℕ) := by
  rintro ⟨f, hf, hmem⟩
  let g : sources → targets := fun a => ⟨f a, target_mem a.property (hmem a).1 (hmem a).2⟩
  have hg : Function.Injective g := by
    intro a b he
    exact hf (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe, source_card, target_card] at hc
  omega

/-- The same obstruction applies to a proposed matching of the entire
retained set, since the eleven sources above are retained inputs. -/
theorem no_full_retained_target_max_matching :
    ¬ ∃ f : retained slope cutoff affine → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ favorable cutoff affine ∧ Nat.maxPrimeFac (affine (f a)) ∣ (a : ℕ) := by
  rintro ⟨f,hf,hmem⟩
  let embed : sources → retained slope cutoff affine :=
    fun a => ⟨a,sources_retained a a.property⟩
  have hembed : Function.Injective embed := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : retained slope cutoff affine => (x : ℕ)) h)
  exact no_target_max_matching ⟨f ∘ embed,hf.comp hembed,fun a => hmem (embed a)⟩

/-- An explicit repair when all target prime factors may be used. -/
def sharedPrimeWitness (a : ℕ) : ℕ :=
  if a=9946 then 1 else if a=14919 then 2 else if a=19498 then 3 else
  if a=19892 then 7 else if a=20338 then 9 else if a=29247 then 8 else
  if a=29838 then 15 else if a=30507 then 14 else if a=38996 then 19 else
  if a=39784 then 21 else if a=40676 then 25 else 0

set_option maxRecDepth 100000 in
lemma witness_inj : ∀ a ∈ sources, ∀ b ∈ sources,
    sharedPrimeWitness a = sharedPrimeWitness b → a=b := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma witness_properties : ∀ a ∈ sources,
    1 ≤ sharedPrimeWitness a ∧ sharedPrimeWitness a ≤ 25 ∧
      Nat.maxPrimeFac (sharedPrimeWitness a) ≤ Nat.maxPrimeFac (affine (sharedPrimeWitness a)) ∧
      1 < a.gcd (affine (sharedPrimeWitness a)) := by
  decide +kernel

/-- The eleven-source obstruction disappears for the original shared-prime
edge condition: these sources can even be matched to targets at most 25.
This finite matching is not a universal matching theorem. -/
theorem sources_have_shared_prime_matching :
    ∃ f : sources → ℕ, Function.Injective f ∧
      ∀ a, f a ≤ 25 ∧ f a ∈ favorable cutoff affine ∧
        1 < (a : ℕ).gcd (affine (f a)) := by
  refine ⟨fun a => sharedPrimeWitness a,?_,?_⟩
  · intro a b h
    exact Subtype.ext (witness_inj a a.property b b.property h)
  · intro a
    obtain ⟨h1,h25,hP,hgcd⟩ := witness_properties a a.property
    refine ⟨h25,mem_filter.mpr ⟨mem_Icc.mpr ⟨h1,?_⟩,hP⟩,hgcd⟩
    exact h25.trans (by norm_num [cutoff])

end Erdos371TargetMaxMatchingObstruction

#print axioms Erdos371TargetMaxMatchingObstruction.no_target_max_matching
#print axioms Erdos371TargetMaxMatchingObstruction.no_full_retained_target_max_matching

#print axioms Erdos371TargetMaxMatchingObstruction.sources_have_shared_prime_matching
