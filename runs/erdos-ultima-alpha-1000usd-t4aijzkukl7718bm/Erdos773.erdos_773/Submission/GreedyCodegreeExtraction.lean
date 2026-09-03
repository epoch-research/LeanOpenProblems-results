import Submission.GreedyCodegreeGuardControls

/-!
Finite independent-set extraction without linearity. All stochastic and
profile hypotheses are discharged by explicit finite numerical conditions.
No particular long horizon is claimed to satisfy these conditions here.
-/
namespace Erdos773.GreedyCodegreeExtraction
open Finset GreedyHypergraphState StoppedGreedyMoments
open GreedyTrackedState FiniteKernelCrossing GreedyProfileRecords GreedyProfileGuard
open GreedyCodegreeGuardControls GreedyRecordedCrossing FourUniformRegularization
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def cost (p : Parameters) (k C T : ℕ) (j : Fin 3) (lower : Bool) (b : ℝ) : ℝ :=
  Real.exp (-(width p j 0)^2/(4*((∑ n ∈ range T, GreedyCodegreeGuardControls.variance p k C j lower n)+b*width p j 0)))

def totalCost (p : Parameters) (k C T : ℕ) (b : Fin 3 → Bool → ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ lower : Bool, cost p k C T j lower (b j lower)

lemma crossing_tail {p : Parameters} {H : Finset (Finset α)} (k : ℕ)
    (hk : ∀ a b : α, a ≠ b → pairDegree H a b ≤ k)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hprom : PromotionBounds p T B2 B3) (j : Fin 3) (u : α) (lower : Bool) (b : ℝ) (hb : 0 < b)
    (hcap : ∀ n < T, GreedyCodegreeGuardControls.rawCap p k C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b) :
    hit (GreedyTrackedState.kernel H L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3)) (crossing p H T j u lower)
      0 T (initial H T) ≤ cost p k C T j lower b := by
  exact GreedyRecordedCrossing.first_crossing (GreedyCodegreeGuardControls.control k hk hfour hh hprom j u lower b hcap)
    (width p j 0) hb (width_pos (by linarith only [hh.bounds.d_one_le]) hh.rho_pos j 0)

/-- All six signed tests at all vertices, on one shared kernel. -/
theorem profile_tail {p : Parameters} {H : Finset (Finset α)} (k : ℕ)
    (hk : ∀ a b : α, a ≠ b → pairDegree H a b ≤ k)
    (hfour : ∀ e ∈ H, e.card ≤ 4) {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ)
    (hprom : PromotionBounds p T B2 B3) (b : Fin 3 → Bool → ℝ) (hb : ∀ j lower, 0 < b j lower)
    (hcap : ∀ j lower n, n < T →
      GreedyCodegreeGuardControls.rawCap p k C j n+|signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b j lower) :
    hit (GreedyTrackedState.kernel H L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3))
      (fun n s => ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s)
      0 T (initial H T) ≤ (Fintype.card α:ℝ)*totalCost p k C T b := by
  let P : (Fin 3 × α × Bool) → ℕ → Tracked H T → Prop :=
    fun i => crossing p H T i.1 i.2.1 i.2.2
  have heq : (fun n s => ∃ i ∈ (univ : Finset (Fin 3 × α × Bool)), P i n s) =
      (fun n s => ∃ (j : Fin 3) (u : α) (lower : Bool), crossing p H T j u lower n s) := by
    funext n s
    apply propext
    simp only [P,mem_univ,true_and,Prod.exists]
  have hu := hit_union_bound (GreedyTrackedState.kernel H L T (GreedyCodegreeProfileGuard.guard p H L T C B2 B3))
    (univ : Finset (Fin 3 × α × Bool)) P 0 T (initial H T)
  rw [heq] at hu
  apply hu.trans
  calc
    _ ≤ ∑ i : Fin 3 × α × Bool, cost p k C T i.1 i.2.2 (b i.1 i.2.2) := by
      apply sum_le_sum
      intro i hi
      exact crossing_tail k hk hfour hh hprom i.1 i.2.1 i.2.2 _ (hb _ _) (hcap _ _)
    _ = _ := by
      simp only [totalCost,Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul,← mul_sum]

/-- A nonlinear full-run certificate. The scalar failure and promotion
    conditions are explicit; no early-stop alternative or path assumption
    remains in the conclusion. These conditions are not asserted here. -/
theorem independent_of_certificate {p : Parameters} {H : Finset (Finset α)}
    (hfour : ∀ e ∈ H, e.card = 4)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (hV : (Fintype.card α:ℝ) = p.V)
    (hregular : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (D k m A : ℕ) (hm : 36 ≤ m) (hAm : A ≤ m)
    (hvolume : Fintype.card α ≤ m^A)
    (hD : ∀ u : α, HypergraphDegreeTrim.degree H u ≤ D)
    (hk : ∀ a b : α, a ≠ b → pairDegree H a b ≤ k)
    (hDb : D ≤ m^300) (hkb : k ≤ m^3)
    {L T C B2 B3 : ℕ} {τ : ℝ} (hh : Horizon p L T C τ) (hTL : T ≤ L)
    (hp : (T:ℝ)/L ≤ 1/(m:ℝ)^97)
    (hC : 16*k^2*m^15 ≤ C) (hB2 : 288*m^133 ≤ B2) (hB3 : 54*m^274 ≤ B3)
    (hprom : PromotionBounds p T B2 B3)
    (b : Fin 3 → Bool → ℝ) (hb : ∀ j lower, 0 < b j lower)
    (hcap : ∀ j lower n, n < T →
      GreedyCodegreeGuardControls.rawCap p k C j n+
        |signedProfile p j lower (n+1)-signedProfile p j lower n| ≤ b j lower)
    (hfailure : 8/(m:ℝ)^2+(Fintype.card α:ℝ)*totalCost p k C T b < 1) :
    ∃ I : Finset α, Independent H I ∧ I.card = T := by
  apply GreedyCodegreeProfileGuard.full_run_of_goodPath hfour hV hregular hh
  apply goodPath_of_hit_lt_one
  have haux := GreedyNonlinearGuardTails.auxiliary_tail hfour hinter D k m A hm hAm
    hvolume hD hk hDb hkb L T hh.L_pos hTL hp C B2 B3 hC hB2 hB3
    (GreedyCodegreeProfileGuard.guard p H L T C B2 B3)
  have hprof := profile_tail k hk (fun e he => (hfour e he).le) hh hprom b hb hcap
  exact (hit_or_bound (GreedyTrackedState.kernel H L T
      (GreedyCodegreeProfileGuard.guard p H L T C B2 B3))
    (fun _ s => GreedyNonlinearGuardTails.auxiliaryBad H C B2 B3 s.chosen)
    (fun n s => ∃ j u lower, crossing p H T j u lower n s) 0 T (initial H T)).trans_lt
      ((add_le_add haux hprof).trans_lt hfailure)

#print axioms crossing_tail
#print axioms profile_tail
#print axioms independent_of_certificate
end
end Erdos773.GreedyCodegreeExtraction
