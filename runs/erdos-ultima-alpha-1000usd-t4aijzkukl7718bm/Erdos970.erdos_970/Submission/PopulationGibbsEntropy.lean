import Submission.FiniteGibbsEntropy
import Submission.PopulationLowCountBennett

/-! Tensorized entropy for the actual survivor count of a finite population.
The coefficient retains every row cap and its exponential tilt cost. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling CoverFibers
set_option maxHeartbeats 2000000

lemma mean_fin_eq_residueMean (p : ℕ) (f : Fin p → ℝ) : mean f = residueMean p f := by
  simp only [mean,residueMean,Fintype.card_fin]

lemma mean_phase_eq_phaseMean (P : Finset ℕ) (f : Phase P → ℝ) : mean f = phaseMean P f := by
  unfold mean phaseMean
  congr 1
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin,Nat.cast_prod]

lemma phase_nonempty (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) : Nonempty (Phase P) :=
  ⟨fun p => ⟨0,hP p.val p.property⟩⟩

lemma mean_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (f : Phase (insert p P) → ℝ) : mean f =
      mean (fun r : Phase P => mean (fun a : Fin p => f (extendPhase P p r a))) := by
  simp_rw [mean_phase_eq_phaseMean,mean_fin_eq_residueMean]
  exact phaseMean_insert P p hp f

lemma entropy_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (f : Phase (insert p P) → ℝ) : entropy f =
      jointEntropy (fun (r : Phase P) (a : Fin p) => f (extendPhase P p r a)) := by
  unfold entropy jointEntropy
  rw [mean_insert P p hp,mean_insert P p hp]

lemma classHits_mono {S T : Finset ℕ} (hST : S ⊆ T) (p : ℕ) (a : Fin p) :
    classHits S p a ≤ classHits T p a := by
  unfold classHits
  exact sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by split_ifs <;> norm_num)

lemma populationSurvivors_insert_avoid (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) :
    populationSurvivors S (insert p P) (extendPhase P p r a) =
      avoidClass (populationSurvivors S P r) p a := by
  classical
  ext x
  simp only [populationSurvivors,avoidClass,mem_filter]
  constructor
  · rintro ⟨hx,ha⟩
    refine ⟨⟨hx,?_⟩,?_⟩
    · intro q
      simpa only [extendPhase_old P p hp r a q] using
        ha ⟨q.val,mem_insert_of_mem q.property⟩
    · simpa only [extendPhase_new] using ha ⟨p,mem_insert_self p P⟩
  · rintro ⟨⟨hx,ho⟩,hn⟩
    refine ⟨hx,?_⟩
    intro q
    by_cases hq : q.val = p
    · have he : q = ⟨p,mem_insert_self p P⟩ := Subtype.ext hq
      cases he
      simpa only [extendPhase_new] using hn
    · have hqP : q.val ∈ P := (mem_insert.mp q.property).resolve_left hq
      have he : q = ⟨(⟨q.val,hqP⟩ : P).val,mem_insert_of_mem hqP⟩ := rfl
      rw [he,extendPhase_old P p hp r a ⟨q.val,hqP⟩]
      exact ho ⟨q.val,hqP⟩

lemma populationSurvivors_avoid_comm (S P : Finset ℕ) (p : ℕ) (a : Fin p) (r : Phase P) :
    populationSurvivors (avoidClass S p a) P r =
      avoidClass (populationSurvivors S P r) p a := by
  classical
  ext x
  simp only [populationSurvivors,avoidClass,mem_filter,and_assoc,and_comm]

noncomputable def count (S P : Finset ℕ) (r : Phase P) : ℝ :=
  (populationSurvivors S P r).card

lemma count_insert_remaining (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) :
    count S (insert p P) (extendPhase P p r a) = remainingCount (populationSurvivors S P r) p a := by
  unfold count remainingCount
  rw [populationSurvivors_insert_avoid S P p hp r a]

lemma count_insert_avoid (S P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) :
    count S (insert p P) (extendPhase P p r a) = count (avoidClass S p a) P r := by
  unfold count
  rw [populationSurvivors_insert_avoid S P p hp r a,populationSurvivors_avoid_comm]

lemma count_empty (S : Finset ℕ) (r : Phase ∅) : count S ∅ r = S.card := by
  classical
  simp [count,populationSurvivors]

lemma residue_entropy_cap (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (t B : ℝ)
    (ht : 0 ≤ t) (hB : 0 ≤ B) (hcap : ∀ a : Fin p, classHits S p a ≤ B) :
    entropy (fun a => exp (-t*remainingCount S p a)) ≤
      t^2*((1+exp (t*B))*B/p)*mean (fun a => exp (-t*remainingCount S p a)*remainingCount S p a) := by
  letI : Nonempty (Fin p) := ⟨⟨0,hp⟩⟩
  have he := entropy_exp_le_resampling (remainingCount S p) t
  have hr := mul_le_mul_of_nonneg_left (gibbs_resampling_second_moment S p hp t B ht hB hcap)
    (sq_nonneg t)
  simp_rw [mean_fin_eq_residueMean] at he ⊢
  exact he.trans (by convert hr using 1; ring)

noncomputable def entropyCapBudget (P : Finset ℕ) (B : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, (1+exp (t*B p))*B p/p

/-- Genuine product tensorization with an explicit state-independent row cap.
No average row variance or independent-survivor approximation is used. -/
theorem population_entropy_cap (P S : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (B : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcap : ∀ p ∈ P, ∀ a : Fin p, classHits S p a ≤ B p) :
    entropy (fun r : Phase P => exp (-t*count S P r)) ≤
      t^2*entropyCapBudget P B t*mean (fun r => exp (-t*count S P r)*count S P r) := by
  classical
  induction P using Finset.induction_on generalizing S with
  | empty =>
    letI : Nonempty (Phase ∅) := phase_nonempty ∅ (by simp)
    simp only [count_empty,entropy,mean_const,sub_self,entropyCapBudget,sum_empty,mul_zero,zero_mul,le_refl]
  | @insert p P hp ih =>
    have hp0 := hP p (mem_insert_self p P)
    have hPo : ∀ q ∈ P, 0 < q := fun q hq => hP q (mem_insert_of_mem hq)
    have hBo : ∀ q ∈ P, 0 ≤ B q := fun q hq => hB q (mem_insert_of_mem hq)
    letI : Nonempty (Phase P) := phase_nonempty P hPo
    letI : Nonempty (Fin p) := ⟨⟨0,hp0⟩⟩
    let f := fun (r : Phase P) (a : Fin p) => exp (-t*count S (insert p P) (extendPhase P p r a))
    let N := fun (r : Phase P) (a : Fin p) => count S (insert p P) (extendPhase P p r a)
    let c := (1+exp (t*B p))*B p/p
    let D := entropyCapBudget P B t
    have hnew (r : Phase P) : entropy (f r) ≤ t^2*c*mean (fun a => f r a*N r a) := by
      have hc : ∀ a : Fin p, classHits (populationSurvivors S P r) p a ≤ B p := fun a =>
        (classHits_mono (filter_subset _ _) p a).trans (hcap p (mem_insert_self p P) a)
      have hh := residue_entropy_cap (populationSurvivors S P r) p hp0 t (B p) ht
        (hB p (mem_insert_self p P)) hc
      simpa only [f,N,c,count_insert_remaining S P p hp] using hh
    have hold (a : Fin p) : entropy (fun r => f r a) ≤ t^2*D*mean (fun r => f r a*N r a) := by
      have hc : ∀ q ∈ P, ∀ b : Fin q, classHits (avoidClass S p a) q b ≤ B q :=
        fun q hq b => (classHits_mono (filter_subset _ _) q b).trans
          (hcap q (mem_insert_of_mem hq) b)
      have hh := ih (avoidClass S p a) hPo hBo hc
      simpa only [f,N,D,count_insert_avoid S P p hp] using hh
    have htwo := entropy_two_coordinate f (fun r a => exp_pos _)
    have hn := mean_mono hnew
    have ho := mean_mono hold
    rw [mean_mul] at hn ho
    rw [mean_comm (fun (a : Fin p) (r : Phase P) => f r a*N r a)] at ho
    have hfin := htwo.trans (add_le_add hn ho)
    rw [entropy_insert P p hp]
    have hb : entropyCapBudget (insert p P) B t = c+D := by
      simp only [entropyCapBudget,sum_insert hp,c,D]
    rw [hb,mean_insert P p hp]
    convert hfin using 1
    dsimp only [f,N]
    ring

#print axioms residue_entropy_cap
#print axioms population_entropy_cap
end Erdos970.FiniteGibbs
