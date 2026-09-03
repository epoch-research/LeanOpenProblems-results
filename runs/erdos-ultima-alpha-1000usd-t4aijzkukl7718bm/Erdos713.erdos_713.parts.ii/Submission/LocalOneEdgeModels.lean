import FormalConjecturesUtil

/-! Consistent bounded-size local models can have a large global objective.
This is an obstruction to bounded local marginal relaxations, not a proof or
disproof of the graph exponent conjecture. -/
open Finset
namespace Erdos713LocalOneEdgeModels
set_option maxHeartbeats 1000000
variable {ι : Type*} [DecidableEq ι]

/-- Expectation for a signed model supported on the empty set and singleton
sets. It is a probability model whenever 0<=p and p*|S|<=1. -/
noncomputable def mean (S : Finset ι) (p : ℝ) (F : Finset ι → ℝ) : ℝ :=
  (1 - p * S.card) * F ∅ + p * ∑ e ∈ S, F {e}

omit [DecidableEq ι] in
lemma mean_const (S : Finset ι) (p c : ℝ) : mean S p (fun _ => c) = c := by
  simp only [mean, sum_const, nsmul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma mean_add (S : Finset ι) (p : ℝ) (F G : Finset ι → ℝ) :
    mean S p (fun R => F R + G R) = mean S p F + mean S p G := by
  simp only [mean, sum_add_distrib]
  ring

omit [DecidableEq ι] in
lemma mean_smul (S : Finset ι) (p c : ℝ) (F : Finset ι → ℝ) :
    mean S p (fun R => c * F R) = c * mean S p F := by
  simp only [mean, ← mul_sum]
  ring

omit [DecidableEq ι] in
lemma mean_nonneg (S : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hS : p * S.card ≤ 1) {P : Finset ι → Prop}
    (hEmpty : P ∅) (hSingle : ∀ e, P {e}) (F : Finset ι → ℝ)
    (hF : ∀ R, R ⊆ S → P R → 0 ≤ F R) : 0 ≤ mean S p F := by
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hS) (hF ∅ (empty_subset _) hEmpty)
  · exact mul_nonneg hp (sum_nonneg fun e he =>
      hF {e} (singleton_subset_iff.mpr he) (hSingle e))

/-- Marginals on smaller variable sets agree exactly, not just asymptotically. -/
lemma mean_restrict {S T : Finset ι} (hTS : T ⊆ S) (p : ℝ) (F : Finset ι → ℝ) :
    mean S p (fun R => F (R ∩ T)) = mean T p F := by
  have hdiff : (∑ e ∈ S \ T, F ({e} ∩ T)) = ((S \ T).card : ℝ) * F ∅ := by
    calc
      (∑ e ∈ S \ T, F ({e} ∩ T)) = ∑ _e ∈ S \ T, F ∅ := by
        apply sum_congr rfl
        intro e he
        rw [singleton_inter_of_notMem (mem_sdiff.mp he).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hsmall : (∑ e ∈ T, F ({e} ∩ T)) = ∑ e ∈ T, F {e} := by
    apply sum_congr rfl
    intro e he
    rw [singleton_inter_of_mem he]
  have hcard : ((S \ T).card : ℝ) = (S.card : ℝ) - T.card := by
    rw [card_sdiff_of_subset hTS, Nat.cast_sub (card_le_card hTS)]
  dsimp [mean]
  rw [empty_inter, ← sum_sdiff hTS, hdiff, hsmall, hcard]
  ring

noncomputable def bit (e : ι) (R : Finset ι) : ℝ := if e ∈ R then 1 else 0

lemma mean_bit {S : Finset ι} {e : ι} (he : e ∈ S) (p : ℝ) :
    mean S p (bit e) = p := by
  simp [mean, bit, he]

omit [DecidableEq ι] in
lemma mean_centered_square (S : Finset ι) (p : ℝ) :
    mean S p (fun R => ((R.card : ℝ) - p * S.card) ^ 2) =
      p * S.card - (p * S.card) ^ 2 := by
  simp only [mean, card_empty, Nat.cast_zero, card_singleton, Nat.cast_one,
    sum_const, nsmul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- The same functional is not globally positive beyond its permitted local
level. Thus these models are not claimed to satisfy global SOS positivity. -/
lemma negative_square_beyond_level (S : Finset ι) (L : ℕ) (hL : 0 < L)
    (hS : L < S.card) :
    ∃ F : Finset ι → ℝ, (∀ R, 0 ≤ F R) ∧ mean S (1 / (L : ℝ)) F < 0 := by
  refine ⟨fun R => ((R.card : ℝ) - (1 / (L : ℝ)) * S.card) ^ 2,
    fun R => sq_nonneg _, ?_⟩
  rw [mean_centered_square]
  have h : (1 : ℝ) < (1 / (L : ℝ)) * S.card := by
    rw [one_div_mul_eq_div, lt_div_iff₀ (show (0 : ℝ) < L by exact_mod_cast hL)]
    simpa only [one_mul] using (show (L : ℝ) < S.card by exact_mod_cast hS)
  nlinarith

/-- Positive normalized linear expectations on small variable sets, supported
on feasible assignments and consistent under every restriction. -/
structure LocalModel (P : Finset ι → Prop) (L : ℕ) where
  value : Finset ι → (Finset ι → ℝ) → ℝ
  constant : ∀ S c, value S (fun _ => c) = c
  add : ∀ S F G, value S (fun R => F R + G R) = value S F + value S G
  smul : ∀ S c F, value S (fun R => c * F R) = c * value S F
  nonneg : ∀ S, S.card ≤ L → ∀ F,
    (∀ R, R ⊆ S → P R → 0 ≤ F R) → 0 ≤ value S F
  restrict : ∀ S T, T ⊆ S → S.card ≤ L → ∀ F,
    value S (fun R => F (R ∩ T)) = value T F

/-- Every feasibility notion permitting the empty assignment and each
singleton has the same local model, with marginal 1/L for every variable. -/
noncomputable def oneEdgeModel (P : Finset ι → Prop) (L : ℕ) (hL : 0 < L)
    (hEmpty : P ∅) (hSingle : ∀ e, P {e}) : LocalModel P L where
  value S := mean S (1 / (L : ℝ))
  constant S c := mean_const S _ c
  add S F G := mean_add S _ F G
  smul S c F := mean_smul S _ c F
  nonneg S hS F hF := by
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    apply mean_nonneg S (by positivity) _ hEmpty hSingle F hF
    rw [one_div_mul_eq_div, div_le_one hLr]
    exact_mod_cast hS
  restrict S T hTS _ F := mean_restrict hTS _ F

lemma oneEdgeModel_bit (P : Finset ι → Prop) (L : ℕ) (hL : 0 < L)
    (hEmpty : P ∅) (hSingle : ∀ e, P {e}) (e : ι) :
    (oneEdgeModel P L hL hEmpty hSingle).value {e} (bit e) = 1 / (L : ℝ) :=
  mean_bit (mem_singleton_self e) _

/-- A set of edges of a complete bipartite graph is a matching precisely
when each of its two coordinate projections is injective. -/
def Matching {A B : Type*} (R : Finset (A × B)) : Prop :=
  Set.InjOn Prod.fst (R : Set (A × B)) ∧ Set.InjOn Prod.snd (R : Set (A × B))

lemma matching_empty {A B : Type*} : Matching (∅ : Finset (A × B)) := by
  constructor <;> intro x hx <;> simp at hx

lemma matching_singleton {A B : Type*} [DecidableEq A] [DecidableEq B] (e : A × B) :
    Matching ({e} : Finset (A × B)) := by
  constructor <;> intro x hx y hy _ <;>
    simpa only [Finset.mem_coe, mem_singleton] using (show x = e from mem_singleton.mp hx).trans
      (mem_singleton.mp hy).symm

lemma matching_card_le {A B : Type*} [Fintype A] [DecidableEq A]
    (R : Finset (A × B)) (hR : Matching R) : R.card ≤ Fintype.card A := by
  calc
    R.card = (R.image Prod.fst).card := (card_image_iff.mpr hR.1).symm
    _ ≤ Fintype.card A := card_le_univ _

/-- At any fixed positive local level, these models fail every constant-factor
upper approximation to the matching optimization, whose feasible edge count
is at most n. The local objective, in contrast, is n^2/L. -/
theorem matching_local_gap (L : ℕ) (hL : 0 < L) (K : ℝ) :
    ∃ n : ℕ, 0 < n ∧
      (∀ R : Finset (Fin n × Fin n), Matching R → R.card ≤ n) ∧
      ∃ M : LocalModel (@Matching (Fin n) (Fin n)) L,
        K * n < ∑ e : Fin n × Fin n, M.value {e} (bit e) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (K * L))
  have hnR : (0 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hKL : K * (L : ℝ) < n := (le_max_right _ _).trans_lt hn
  let M := oneEdgeModel (@Matching (Fin n) (Fin n)) L hL matching_empty matching_singleton
  refine ⟨n, hnpos, ?_, M, ?_⟩
  · intro R hR
    simpa only [Fintype.card_fin] using matching_card_le R hR
  · have hsum : (∑ e : Fin n × Fin n, M.value {e} (bit e)) = (n : ℝ) ^ 2 / L := by
      simp only [M, oneEdgeModel_bit, sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hsum, lt_div_iff₀ (show (0 : ℝ) < L by exact_mod_cast hL)]
    nlinarith [mul_lt_mul_of_pos_right hKL hnR]

#print axioms mean_restrict
#print axioms negative_square_beyond_level
#print axioms oneEdgeModel
#print axioms matching_local_gap
end Erdos713LocalOneEdgeModels
