import Submission.Hypergraph

/-! Finite event probabilities and indexed union bounds for the actual
Bernoulli product weights. -/
namespace Erdos773.BernoulliEvents
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def prob (p : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ f : α → Bool, if P (selected f) then trialWeight p f else 0

lemma nonneg (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (P : Finset α → Prop) : 0≤prob p P := by
  apply sum_nonneg
  intro f hf
  split_ifs
  · exact trialWeight_nonneg hp hp1 f
  · exact le_refl _

lemma mono (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (P Q : Finset α → Prop)
    (h : ∀ R, P R → Q R) : prob p P≤prob p Q := by
  apply sum_le_sum
  intro f hf
  split_ifs with hP hQ
  all_goals try exact le_refl _
  all_goals try exact trialWeight_nonneg hp hp1 f
  exact (hQ (h _ hP)).elim

/-- An indexed covering bound, valid with dependent or repeated events. -/
theorem cover_bound (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (S : Finset β)
    (P : β → Finset α → Prop) (Bad : Finset α → Prop)
    (hcover : ∀ R, Bad R → ∃ i∈S, P i R) : prob p Bad≤∑ i∈S, prob p (P i) := by
  have hpoint (f : α → Bool) : (if Bad (selected f) then trialWeight p f else 0)≤
      ∑ i∈S, if P i (selected f) then trialWeight p f else 0 := by
    by_cases hb : Bad (selected f)
    · obtain ⟨i,hi,hP⟩ := hcover _ hb
      have hh := single_le_sum (s := S) (f := fun i => if P i (selected f) then trialWeight p f else 0)
        (fun i hi => by dsimp only; split_ifs; exact trialWeight_nonneg hp hp1 f; exact le_refl _) hi
      simpa only [if_pos hb,if_pos hP] using hh
    · rw [if_neg hb]
      apply sum_nonneg
      intro i hi
      split_ifs
      · exact trialWeight_nonneg hp hp1 f
      · exact le_refl _
  have hh := sum_le_sum (s := (univ : Finset (α → Bool))) (fun f _ => hpoint f)
  rw [sum_comm] at hh
  exact hh

lemma union_bound (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (P Q : Finset α → Prop) :
    prob p (fun R => P R ∨ Q R)≤prob p P+prob p Q := by
  have hh := cover_bound p hp hp1 (univ : Finset Bool) (fun b => if b then P else Q) (fun R => P R ∨ Q R) (by
    intro R h
    rcases h with h | h
    · exact ⟨true,mem_univ _,h⟩
    · exact ⟨false,mem_univ _,h⟩)
  simpa [add_comm] using hh

/-- A deterministic upper cap makes a mean-dependent exponential term
uniform in small families. If mu<L, the stated upper-tail event is empty. -/
theorem capped_exponential_tail (p : ℝ) (X : Finset α → ℝ) (n μ η L M E : ℝ)
    (hX : ∀ R, X R≤n) (hμ : 0≤μ) (hη : 0≤η) (hM : 0<M) (hE : 0≤E)
    (htail : prob p (fun R => n-(1-η)*μ+L≤X R)≤Real.exp (-η^2*μ/(2*M))+E) :
    prob p (fun R => n-(1-η)*μ+L≤X R)≤Real.exp (-η^2*L/(2*M))+E := by
  by_cases hLμ : L≤μ
  · apply htail.trans
    apply add_le_add _ le_rfl
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : 0≤2*M)
    have hh := mul_le_mul_of_nonneg_left hLμ (sq_nonneg η)
    nlinarith only [hh]
  · have hbad (R : Finset α) : ¬n-(1-η)*μ+L≤X R := by
      have hh := hX R
      have hz := mul_nonneg hη hμ
      intro he
      linarith only [hh,hz,he,lt_of_not_ge hLμ]
    simp only [prob,if_neg (hbad _),sum_const_zero]
    exact add_nonneg (Real.exp_pos _).le hE

#print axioms cover_bound
#print axioms union_bound
#print axioms capped_exponential_tail
end
end Erdos773.BernoulliEvents
