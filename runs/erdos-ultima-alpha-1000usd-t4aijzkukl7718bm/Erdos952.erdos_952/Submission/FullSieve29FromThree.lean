import Submission.FullSieve29Result
import Submission.ExceptionSieveTen
import Submission.PrimeStepSubdivisionCounterexample

/-! A fixed-bound example: cutoff 29 admits escape from the prime seed 3,
but cutoff 89 rejects it. Neither fact concerns arbitrary jump bounds. -/
namespace Erdos952Investigation.FullSieve29FromThree
open FiniteSieveReduction ExceptionSieveReduction ExceptionSieveDecision
open Sieve729Ten (embed embed_injective embed_step_norm sqDist)
set_option maxHeartbeats 0
set_option maxRecDepth 3000

private def points : Fin 27 → GaussianInt := ![(⟨3,0⟩ : GaussianInt),(⟨5,2⟩ : GaussianInt),(⟨7,2⟩ : GaussianInt),(⟨9,4⟩ : GaussianInt),(⟨11,6⟩ : GaussianInt),(⟨12,7⟩ : GaussianInt),(⟨14,9⟩ : GaussianInt),(⟨16,9⟩ : GaussianInt),(⟨17,8⟩ : GaussianInt),(⟨19,10⟩ : GaussianInt),(⟨21,10⟩ : GaussianInt),(⟨23,12⟩ : GaussianInt),(⟨25,12⟩ : GaussianInt),(⟨26,11⟩ : GaussianInt),(⟨28,13⟩ : GaussianInt),(⟨30,11⟩ : GaussianInt),(⟨32,13⟩ : GaussianInt),(⟨34,15⟩ : GaussianInt),(⟨35,16⟩ : GaussianInt),(⟨35,18⟩ : GaussianInt),(⟨33,20⟩ : GaussianInt),(⟨35,22⟩ : GaussianInt),(⟨35,24⟩ : GaussianInt),(⟨35,26⟩ : GaussianInt),(⟨33,28⟩ : GaussianInt),(⟨31,30⟩ : GaussianInt),(⟨30,29⟩ : GaussianInt)]

private lemma points_prime (i : Fin 27) : Prime (points i) := by
  fin_cases i
  · exact gaussian_prime_three
  all_goals
    apply PrimeStepSubdivisionCounterexample.prime_of_prime_norm
    norm_num [points,gaussian_norm_sq]

private lemma points_step : ∀ i : Fin 26,
    points i.castSucc ≠ points i.succ ∧ (points i.succ-points i.castSucc).norm < 9 := by
  decide +kernel

lemma seed_prime_path : (primeGraph 9).Reachable (3 : GaussianInt) (⟨30,29⟩ : GaussianInt) := by
  have ha (i : Fin 26) : (primeGraph 9).Adj (points i.castSucc) (points i.succ) :=
    ⟨points_prime _,points_prime _,points_step i⟩
  have hr (i : Fin 27) : (primeGraph 9).Reachable (3 : GaussianInt) (points i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih => exact ih.trans (ha i).reachable
  exact hr (26 : Fin 27)

lemma good_not_row27 {z : ℤ × ℤ} (hz : FullSieve29.Good z) : z.1 ≠ 27 := by
  intro he
  have hh := hz.2.1
  rw [he] at hh
  norm_num at hh

lemma good_not_row28 {z : ℤ × ℤ} (hz : FullSieve29.Good z) : z.1 ≠ 28 := by
  intro he
  have hh := hz.2.2.1
  rw [he] at hh
  norm_num at hh

lemma row_lower_closed {z w : ℤ × ℤ} (hz : 29 ≤ z.1) (h : FullSieve29.graph.Adj z w) :
    29 ≤ w.1 := by
  have hs := h.2.2.2
  dsimp only [sqDist] at hs
  have hd : -2 ≤ w.1-z.1 := by nlinarith [sq_nonneg (w.2-z.2)]
  have h27 := good_not_row27 h.2.1
  have h28 := good_not_row28 h.2.1
  omega

lemma embed_norm_large {z : ℤ × ℤ} (hz : 29 ≤ z.1) : (29 : ℤ)^2 < (embed z).norm := by
  rw [Sieve729Ten.embed_norm]
  dsimp only [Sieve729.normPoly]
  nlinarith [sq_nonneg (2*z.2+1),sq_nonneg (z.1-29)]

/-- The certified walk lies in a component trapped above two forbidden rows,
so its entire component avoids the small exceptional norm ball. -/
theorem candidate_wrap_component_infinite :
    {w | (candidateGraph 9 29).Reachable (⟨30,29⟩ : GaussianInt) w}.Infinite := by
  obtain ⟨x,hx0,hx,ha⟩ := (RayReduction.ray_iff_infinite_component FullSieve29.graph (29,0)).mpr
    (FullSieve29.infinite_component_of_wrap FullSieve29.certified_wrap)
  have hrow (n : ℕ) : 29 ≤ (x n).1 := by
    induction n with
    | zero => rw [hx0]
    | succ n ih => exact row_lower_closed ih (ha n)
  have hc (n : ℕ) : Candidate 29 (embed (x n)) :=
    Or.inr ⟨embed_norm_large (hrow n),FullSieve29.good_full_sieve (ha n).1⟩
  have hadj (n : ℕ) : (candidateGraph 9 29).Adj (embed (x n)) (embed (x (n+1))) := by
    refine ⟨hc n,hc (n+1),?_,?_⟩
    · intro he
      have hh := hx (embed_injective he)
      omega
    · rw [embed_step_norm]
      have hh := (ha n).2.2.2
      omega
  apply (RayReduction.ray_iff_infinite_component (candidateGraph 9 29) _).mp
  exact ⟨fun n => embed (x n),by change embed (x 0) = (⟨30,29⟩ : GaussianInt); rw [hx0]; rfl,embed_injective.comp hx,hadj⟩

theorem candidate_seed_infinite :
    {w | (candidateGraph 9 29).Reachable (3 : GaussianInt) w}.Infinite := by
  have hr := seed_prime_path.mono (primeGraph_le 9 29)
  exact candidate_wrap_component_infinite.mono (fun _ hw => hr.trans hw)

theorem cutoffTest_29_true : cutoffTest 9 29 = true :=
  (cutoffTest_true_iff 9 29).mpr candidate_seed_infinite

theorem cutoffTest_89_false : cutoffTest 9 89 = false :=
  ExceptionSieveTen.cutoffTest_false_le_ten 9 (by decide)

theorem prime_seed_component_finite : {w | (primeGraph 9).Reachable (3 : GaussianInt) w}.Finite := by
  exact (ExceptionSieveReduction.component_finite_iff_cutoff 9 3).mpr
    ⟨89,ExceptionSieveTen.cutoff_component_finite 9 (by decide)⟩

#print axioms candidate_seed_infinite
#print axioms cutoffTest_29_true
#print axioms cutoffTest_89_false
#print axioms prime_seed_component_finite
end Erdos952Investigation.FullSieve29FromThree
