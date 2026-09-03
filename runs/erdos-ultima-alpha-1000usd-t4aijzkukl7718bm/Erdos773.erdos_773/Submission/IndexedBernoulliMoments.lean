import Submission.HypergraphSamplingMoments

/-! High moments of indexed uniform witness counts, retaining every overlap
rank. Repeated supports are allowed. Unlike a maximum-degree-only bound,
a one-vertex overlap in an r-witness still pays p^(r-1). -/
namespace Erdos773.IndexedBernoulliMoments
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def incidence (T : Finset β) (C : β → Finset α) (U : Finset α) : ℕ :=
  (T.filter (fun i => U⊆C i)).card

def budget (r q : ℕ) (K : ℕ → ℕ) (p : ℝ) : ℝ :=
  ∑ k∈range (r+1), ((r*q).choose k:ℝ)*K k*p^(r-k)

lemma budget_nonneg (r q : ℕ) (K : ℕ → ℕ) {p : ℝ} (hp : 0≤p) : 0≤budget r q K p := by
  apply sum_nonneg
  intro k hk
  positivity

lemma union_exponent {U V : Finset α} {r : ℕ} (hV : V.card=r) :
    (U∪V).card=U.card+(r-(U∩V).card) := by
  have hh := card_union_add_card_inter U V
  have hi := card_le_card (inter_subset_right : U∩V⊆V)
  omega

/-- An explicit overlap-stratified one-step estimate. -/
lemma union_step (T : Finset β) (C : β → Finset α) (U : Finset α)
    (r q : ℕ) (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p)
    (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card)
    (hU : U.card≤r*q) :
    (∑ i∈T, p^(U∪C i).card) ≤ p^U.card*budget r q K p := by
  have hpoint (i : β) (hi : i∈T) :
      p^(U∪C i).card ≤ p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, if S⊆C i then p^(r-k) else 0) := by
    let S := U∩C i
    have hSr : S.card≤r := (card_le_card inter_subset_right).trans_eq (hr i hi)
    have hSmem : S∈U.powersetCard S.card := mem_powersetCard.mpr ⟨inter_subset_left,rfl⟩
    have hs1 : p^(r-S.card) ≤ ∑ A∈U.powersetCard S.card,
        if A⊆C i then p^(r-S.card) else 0 := by
      have hh := single_le_sum (s := U.powersetCard S.card)
        (f := fun A => if A⊆C i then p^(r-S.card) else 0)
        (fun A hA => by dsimp only; split_ifs <;> positivity) hSmem
      simpa only [show S⊆C i from inter_subset_right,if_true] using hh
    have hs2 : (∑ A∈U.powersetCard S.card, if A⊆C i then p^(r-S.card) else 0) ≤
        ∑ k∈range (r+1), ∑ A∈U.powersetCard k, if A⊆C i then p^(r-k) else 0 := by
      apply single_le_sum (f := fun k => ∑ A∈U.powersetCard k, if A⊆C i then p^(r-k) else 0) (a := S.card)
      · intro k hk
        apply sum_nonneg
        intro A hA
        split_ifs <;> positivity
      · exact mem_range.mpr (by omega)
    rw [union_exponent (hr i hi),pow_add]
    exact mul_le_mul_of_nonneg_left (hs1.trans hs2) (pow_nonneg hp _)
  have hb (k : ℕ) (hk : k∈range (r+1)) :
      (∑ S∈U.powersetCard k, ∑ i∈T, if S⊆C i then p^(r-k) else 0) ≤
        ((r*q).choose k:ℝ)*K k*p^(r-k) := by
    have hk' : k≤r := by simpa only [mem_range,Nat.lt_succ_iff] using hk
    calc
      _ = ∑ S∈U.powersetCard k, (incidence T C S:ℝ)*p^(r-k) := by
        apply sum_congr rfl
        intro S hS
        rw [← sum_filter]
        simp [incidence]
      _ ≤ ∑ _S∈U.powersetCard k, (K k:ℝ)*p^(r-k) := by
        apply sum_le_sum
        intro S hS
        have hSc := (mem_powersetCard.mp hS).2
        have hh := hK S (hSc.trans_le hk')
        rw [hSc] at hh
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (pow_nonneg hp _)
      _ = (U.card.choose k:ℝ)*K k*p^(r-k) := by
        simp only [sum_const,nsmul_eq_mul,card_powersetCard]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast Nat.choose_le_choose k hU
  calc
    _ ≤ ∑ i∈T, p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, if S⊆C i then p^(r-k) else 0) := sum_le_sum hpoint
    _ = p^U.card*(∑ k∈range (r+1),
        ∑ S∈U.powersetCard k, ∑ i∈T, if S⊆C i then p^(r-k) else 0) := by
      rw [← mul_sum,sum_comm]
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum hb) (pow_nonneg hp _)

def jointMoment (T : Finset β) (C : β → Finset α) (p : ℝ) : ℕ → Finset α → ℝ
  | 0,U => p^U.card
  | k+1,U => ∑ i∈T, jointMoment T C p k (U∪C i)

lemma jointMoment_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p) (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    ∀ k U, U.card+r*k≤r*q → jointMoment T C p k U≤p^U.card*(budget r q K p)^k := by
  intro k
  induction k with
  | zero => intro U hU; simp [jointMoment]
  | succ k ih =>
    intro U hU
    have hrec (i : β) (hi : i∈T) : (U∪C i).card+r*k≤r*q := by
      have hh := card_union_le U (C i)
      rw [hr i hi] at hh
      simp only [Nat.mul_succ] at hU
      omega
    calc
      _ ≤ ∑ i∈T, p^(U∪C i).card*(budget r q K p)^k :=
        sum_le_sum (fun i hi => ih (U∪C i) (hrec i hi))
      _ = (∑ i∈T, p^(U∪C i).card)*(budget r q K p)^k := (sum_mul _ _ _).symm
      _ ≤ (p^U.card*budget r q K p)*(budget r q K p)^k :=
        mul_le_mul_of_nonneg_right (union_step T C U r q K p hp hr hK (by omega))
          (pow_nonneg (budget_nonneg r q K hp) _)
      _ = _ := by rw [pow_succ]; ring

section Expectation
variable [Fintype α]

lemma jointMoment_expectation (T : Finset β) (C : β → Finset α) (p : ℝ)
    (k : ℕ) (U : Finset α) :
    jointMoment T C p k U = ∑ f : α → Bool,
      if U⊆selected f then trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^k else 0 := by
  induction k generalizing U with
  | zero => simpa only [jointMoment,pow_zero,mul_one] using (sum_trialWeight_contains p U).symm
  | succ k ih =>
    simp only [jointMoment,ih]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    by_cases hU : U⊆selected f
    · simp only [union_subset_iff,hU,true_and,if_true]
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul,pow_succ]
      ring
    · simp only [union_subset_iff,hU,false_and,if_false,sum_const_zero]

/-- The complete indexed moment bound, with every overlap rank retained. -/
theorem moment_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p : ℝ) (hp : 0≤p) (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    (∑ f : α → Bool, trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^q) ≤
      (budget r q K p)^q := by
  have hh := jointMoment_bound T C r q K p hp hr hK q ∅ (by simp)
  rw [jointMoment_expectation] at hh
  simpa only [empty_subset,if_true,card_empty,pow_zero,one_mul] using hh

/-- Markov tail with the same overlap-sensitive budget. -/
theorem tail_bound (T : Finset β) (C : β → Finset α) (r q : ℕ)
    (K : ℕ → ℕ) (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L)
    (hr : ∀ i∈T, (C i).card=r)
    (hK : ∀ S : Finset α, S.card≤r → incidence T C S≤K S.card) :
    (∑ f : α → Bool, if L≤((T.filter (fun i => C i⊆selected f)).card:ℝ)
      then trialWeight p f else 0) ≤ (budget r q K p/L)^q := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hL q)).mpr
  calc
    _ = ∑ f : α → Bool, if L≤((T.filter (fun i => C i⊆selected f)).card:ℝ)
        then trialWeight p f*L^q else 0 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ ≤ ∑ f : α → Bool, trialWeight p f*((T.filter (fun i => C i⊆selected f)).card:ℝ)^q := by
      apply sum_le_sum
      intro f hf
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le h q) (trialWeight_nonneg hp hp1 f)
      · exact mul_nonneg (trialWeight_nonneg hp hp1 f) (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := moment_bound T C r q K p hp hr hK
end Expectation

#print axioms union_step
#print axioms jointMoment_bound
#print axioms moment_bound
#print axioms tail_bound
end
end Erdos773.IndexedBernoulliMoments
