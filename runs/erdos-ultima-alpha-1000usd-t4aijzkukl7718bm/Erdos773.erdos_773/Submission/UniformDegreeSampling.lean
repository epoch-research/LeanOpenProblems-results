import Submission.HypergraphSamplingMoments

/-! Finite simultaneous sampling with prescribed upper bounds for every
member of a family of induced edge counts, followed by obstruction deletion. -/
namespace Erdos773.UniformDegreeSampling
open Finset HypergraphSamplingMoments
set_option maxHeartbeats 2000000
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

def potential (H : β → Finset (Finset α)) (q : ℕ) (T : ℝ) (B : Finset α) : ℝ :=
  ∑ b : β, (((H b).filter (· ⊆ B)).card/T:ℝ)^q

omit [Fintype α] in
lemma potential_nonneg (H : β → Finset (Finset α)) (q : ℕ) (T : ℝ) (hT : 0<T) (B : Finset α) :
    0 ≤ potential H q T B := by
  apply sum_nonneg
  intro b hb
  exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) hT.le) _

lemma potential_bound (H : β → Finset (Finset α)) (r K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hr : ∀ b, ∀ e ∈ H b, e.card=r)
    (hK : ∀ b a, ((H b).filter (fun e => a ∈ e)).card ≤ K)
    (hcard : ∀ b, ((H b).card:ℝ) ≤ D) :
    (∑ f : α → Bool, trialWeight p f*potential H q T (selected f)) ≤
      (Fintype.card β:ℝ)*((p^r*D+(r*q:ℕ)*K)/T)^q := by
  have hmoment (b : β) :
      (∑ f : α → Bool, trialWeight p f*((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q) ≤
        ((p^r*D+(r*q:ℕ)*K)/T)^q := by
    simp only [div_pow,← mul_div_assoc,← sum_div]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hT.le _)
    apply (moment_bound (H b) r K q p hp hp1 (hr b) (hK b)).trans
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (hcard b) (pow_nonneg hp _)) le_rfl
  calc
    _ = ∑ b : β, ∑ f : α → Bool,
        trialWeight p f*((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q := by
      simp only [potential,mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _b : β, ((p^r*D+(r*q:ℕ)*K)/T)^q := sum_le_sum (fun b _ => hmoment b)
    _ = _ := by simp

/-- An actual subset satisfies ALL link-count caps. The penalty for failure
is the entire carrier size; its high-moment expectation pays for the union
bound without needing an additional cardinality concentration theorem. -/
theorem finite_selection (H : β → Finset (Finset α)) (P : Finset (Finset α))
    (r s K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hr : ∀ b, ∀ e ∈ H b, e.card=r)
    (hK : ∀ b a, ((H b).filter (fun e => a ∈ e)).card ≤ K)
    (hcard : ∀ b, ((H b).card:ℝ) ≤ D)
    (hP : ∀ e ∈ P, e.card=s) (hs : 0<s)
    (hpositive : 0 < p*Fintype.card α-p^s*P.card-
      (Fintype.card α:ℝ)*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q) :
    ∃ B : Finset α, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ b, (((H b).filter (· ⊆ B)).card:ℝ)<T) ∧
      p*Fintype.card α-p^s*P.card-
        (Fintype.card α:ℝ)*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  classical
  let V : ℝ := Fintype.card α
  let cost (f : α → Bool) : ℝ := (selected f).card-(P.filter (· ⊆ selected f)).card-
    V*potential H q T (selected f)
  have hV : 0 ≤ V := Nat.cast_nonneg _
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ cost univ_nonempty
  have hupper : (∑ g : α → Bool, trialWeight p g*cost g) ≤ cost f := by
    calc
      _ ≤ ∑ g : α → Bool, trialWeight p g*cost f :=
        sum_le_sum (fun g hg => mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g))
      _ = _ := by rw [← sum_mul,sum_trialWeight,one_mul]
  have hPsum : (∑ e ∈ P, p^e.card) = p^s*P.card := by
    simp only [sum_congr rfl (fun e he => congrArg (fun j => p^j) (hP e he)),sum_const,nsmul_eq_mul]
    ring
  have hexpect : (∑ g : α → Bool, trialWeight p g*cost g) =
      p*Fintype.card α-p^s*P.card-V*(∑ g : α → Bool, trialWeight p g*potential H q T (selected g)) := by
    simp only [cost,mul_sub,sum_sub_distrib,sum_trialWeight_card,sum_trialWeight_edgeCount,hPsum]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro g hg
    ring
  have hpot := potential_bound H r K q p T D hp hp1 hT hr hK hcard
  have hmul := mul_le_mul_of_nonneg_left hpot hV
  have hlower : p*Fintype.card α-p^s*P.card-
      V*Fintype.card β*((p^r*D+(r*q:ℕ)*K)/T)^q ≤ cost f := by
    rw [hexpect] at hupper
    nlinarith only [hupper,hmul]
  have hpos : 0<cost f := lt_of_lt_of_le hpositive hlower
  have hcaps (b : β) : (((H b).filter (· ⊆ selected f)).card:ℝ)<T := by
    by_contra! hn
    have hratio : 1 ≤ ((((H b).filter (· ⊆ selected f)).card:ℝ)/T) :=
      (one_le_div hT).mpr hn
    have hterm : 1 ≤ ((((H b).filter (· ⊆ selected f)).card:ℝ)/T)^q := one_le_pow₀ hratio
    have hsum : 1 ≤ potential H q T (selected f) := by
      apply hterm.trans
      unfold potential
      apply single_le_sum (f := fun c : β => ((((H c).filter (· ⊆ selected f)).card:ℝ)/T)^q)
      · intro c hc; positivity
      · exact mem_univ b
    have hc : ((selected f).card:ℝ) ≤ V := by
      dsimp [V]
      exact_mod_cast card_le_univ (selected f)
    have hmul := mul_le_mul_of_nonneg_left hsum hV
    have hPnon : (0:ℝ) ≤ (P.filter (· ⊆ selected f)).card := Nat.cast_nonneg _
    dsimp [cost] at hpos
    nlinarith only [hc,hmul,hPnon,hpos]
  obtain ⟨B,hB,hBc,havoid⟩ := delete_forbidden_edges (selected f) (P.filter (· ⊆ selected f))
    (fun e he => card_pos.mp (by rw [hP e (mem_filter.mp he).1]; exact hs))
  refine ⟨B,?_,?_,?_⟩
  · intro e he heB
    exact havoid e (mem_filter.mpr ⟨he,heB.trans hB⟩) heB
  · intro b
    have hc : (((H b).filter (· ⊆ B)).card:ℝ) ≤ ((H b).filter (· ⊆ selected f)).card := by
      exact_mod_cast card_le_card (show (H b).filter (· ⊆ B) ⊆ (H b).filter (· ⊆ selected f) by
        intro e he
        obtain ⟨he,heB⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨he,heB.trans hB⟩)
    exact hc.trans_lt (hcaps b)
  · have hc : ((selected f).card:ℝ) ≤ B.card+(P.filter (· ⊆ selected f)).card := by exact_mod_cast hBc
    have hnon := mul_nonneg hV (potential_nonneg H q T hT (selected f))
    dsimp [cost] at hlower
    nlinarith only [hc,hnon,hlower]

#print axioms potential_bound
#print axioms finite_selection
end
end Erdos773.UniformDegreeSampling
