import Submission.GreedyGuardControls

/-!
A finite independent-set certificate with no remaining guard, drift, or
path-existence assumptions. Its inputs are explicit numerical horizon,
increment-cap, and summed-failure inequalities.
-/
namespace Erdos773.GreedyProfileExtraction
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyLinearDrift GreedyCommonNeighbors
open GreedyTrackedState FiniteKernelCrossing GreedyProfileRecords GreedyProfileGuard
open GreedyGuardControls GreedyRecordedCrossing GreedyConfigurationTails
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Common-neighbor first-hit bound for the actual recorded kernel. Its
    carrier law agrees with the original stopped process even after freezing. -/
theorem auxiliary_tail {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card = 4) (D : ℕ)
    (hD : ∀ u : α, HypergraphDegreeTrim.degree H u ≤ D)
    (L T : ℕ) (hL : 0 < L) (hTL : T ≤ L) (k : ℕ)
    (G : ℕ → Tracked H T → Prop) :
    hit (GreedyTrackedState.kernel H L T G)
      (fun _ s => auxiliaryBad H (16*k) s.chosen) 0 T (initial H T) ≤
        (Fintype.card α:ℝ)^2*(9*D*((T:ℝ)/L)^3/(k+1))^(k+1) := by
  let P : (α × α) → ℕ → Tracked H T → Prop := fun uv _ s =>
    GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*k) s.chosen
  have heq : (fun n s => ∃ uv ∈ (univ : Finset α).offDiag, P uv n s) =
      (fun _ s => auxiliaryBad H (16*k) s.chosen) := by
    funext n s
    apply propext
    simp only [P,auxiliaryBad,mem_offDiag,mem_univ,true_and,Prod.exists]
  have htail (uv : α × α) (huv : uv ∈ (univ : Finset α).offDiag) :
      hit (GreedyTrackedState.kernel H L T G) (P uv) 0 T (initial H T) ≤
        (9*D*((T:ℝ)/L)^3/(k+1))^(k+1) := by
    have huv := (mem_offDiag.mp huv).2.2
    have hmono : ∀ I J : Finset α, I ⊆ J → GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*k) I →
        GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*k) J := by
      intro I J hIJ hp
      obtain ⟨S,hSI,hu,hv,hc⟩ := hp
      exact ⟨S,hSI.trans hIJ,hu,hv,hc⟩
    change hit _ (fun _ (s : Tracked H T) => GreedyCommonNeighbors.prefixBad H uv.1 uv.2 (16*k) s.chosen) _ _ _ ≤ _
    rw [hit_carrier H L T G _ hmono]
    have hh := prefix_common_exponential_tail hfour
      (fun e he f hf hef => (hlin e he f hf hef).trans (by omega))
      uv.1 uv.2 huv D 1 (hD uv.1) (fun a b hab => hlin.pair_degree a b hab) L hL T hTL k
    simpa only [one_pow,mul_one,Nat.cast_one] using hh
  have hu := hit_union_bound (GreedyTrackedState.kernel H L T G) (univ : Finset α).offDiag P 0 T (initial H T)
  rw [heq] at hu
  apply hu.trans
  calc
    _ ≤ ∑ _uv ∈ (univ : Finset α).offDiag, (9*D*((T:ℝ)/L)^3/(k+1))^(k+1) := sum_le_sum htail
    _ = ((univ : Finset α).offDiag.card:ℝ)*(9*D*((T:ℝ)/L)^3/(k+1))^(k+1) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh : (univ : Finset α).offDiag.card ≤ (Fintype.card α)^2 := by
        rw [offDiag_card,card_univ,pow_two]
        exact Nat.sub_le _ _
      exact_mod_cast hh

def cost (p : Parameters) (C T : ℕ) (j : Fin 3) (lower : Bool) (b : ℝ) : ℝ :=
  Real.exp (-(width p j 0)^2/(4*((∑ n ∈ range T, variance p C j lower n)+b*width p j 0)))

def totalCost (p : Parameters) (C T : ℕ) (b : Fin 3 → Bool → ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ lower : Bool, cost p C T j lower (b j lower)

lemma crossing_tail {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (j : Fin 3) (u : α) (lower : Bool) (b : ℝ) (hb : 0 < b)
    (hcap : ∀ n < T, rawCap p C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    hit (GreedyTrackedState.kernel H L T (guard p H L T C)) (crossing p H T j u lower)
      0 T (initial H T) ≤ cost p C T j lower b := by
  exact GreedyRecordedCrossing.first_crossing (control hlin hfour hh j u lower b hcap)
    (width p j 0) hb (width_pos (by linarith only [hh.bounds.d_one_le]) hh.rho_pos j 0)

/-- All six signed tests at all vertices, on one shared kernel. -/
theorem profile_tail {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (b : Fin 3 → Bool → ℝ) (hb : ∀ j lower, 0 < b j lower)
    (hcap : ∀ j lower n, n < T →
      rawCap p C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b j lower) :
    hit (GreedyTrackedState.kernel H L T (guard p H L T C))
      (fun n s => ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s)
      0 T (initial H T) ≤ (Fintype.card α:ℝ)*totalCost p C T b := by
  let P : (Fin 3 × α × Bool) → ℕ → Tracked H T → Prop :=
    fun i => crossing p H T i.1 i.2.1 i.2.2
  have heq : (fun n s => ∃ i ∈ (univ : Finset (Fin 3 × α × Bool)), P i n s) =
      (fun n s => ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s) := by
    funext n s
    apply propext
    simp only [P,mem_univ,true_and,Prod.exists]
  have hu := hit_union_bound (GreedyTrackedState.kernel H L T (guard p H L T C))
    (univ : Finset (Fin 3 × α × Bool)) P 0 T (initial H T)
  rw [heq] at hu
  apply hu.trans
  calc
    _ ≤ ∑ i : Fin 3 × α × Bool, cost p C T i.1 i.2.2 (b i.1 i.2.2) := by
      apply sum_le_sum
      intro i hi
      exact crossing_tail hlin hfour hh i.1 i.2.1 i.2.2 _ (hb _ _) (hcap _ _)
    _ = _ := by
      simp only [totalCost,Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul,← mul_sum]

/-- An independent set of size T follows from a completely explicit finite
    numerical certificate. There are no hidden drift, guard, or early-stop
    assumptions in this theorem. The failure inequality is not asserted here. -/
theorem independent_of_certificate {p : Parameters} {H : Finset (Finset α)} (hlin : Linear H)
    (hfour : ∀ e ∈ H, e.card = 4) (hV : (Fintype.card α:ℝ) = p.V)
    (hregular : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (D : ℕ) (hD : ∀ u : α, HypergraphDegreeTrim.degree H u ≤ D)
    {L T k : ℕ} {τ : ℝ} (hh : Horizon p L T (16*k) τ) (hTL : T ≤ L)
    (b : Fin 3 → Bool → ℝ) (hb : ∀ j lower, 0 < b j lower)
    (hcap : ∀ j lower n, n < T →
      rawCap p (16*k) j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b j lower)
    (hfailure : (Fintype.card α:ℝ)^2*(9*D*((T:ℝ)/L)^3/(k+1))^(k+1)+
      (Fintype.card α:ℝ)*totalCost p (16*k) T b < 1) :
    ∃ I : Finset α, Independent H I ∧ I.card = T := by
  apply full_run_of_goodPath hlin hfour hV hregular hh
  apply goodPath_of_hit_lt_one
  have haux := auxiliary_tail hlin hfour D hD L T hh.L_pos hTL k (guard p H L T (16*k))
  have hprof := profile_tail hlin (fun e he => (hfour e he).le) hh b hb hcap
  exact (hit_or_bound (GreedyTrackedState.kernel H L T (guard p H L T (16*k)))
    (fun _ s => auxiliaryBad H (16*k) s.chosen)
    (fun n s => ∃ j u lower, crossing p H T j u lower n s) 0 T (initial H T)).trans_lt
      ((add_le_add haux hprof).trans_lt hfailure)

#print axioms auxiliary_tail
#print axioms crossing_tail
#print axioms profile_tail
#print axioms independent_of_certificate
end
end Erdos773.GreedyProfileExtraction
