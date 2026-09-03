import Submission.Sieve729TenLogic
import Submission.FiniteSieveReduction

/-! A checker for one ordinary finite-sieve ray, retaining avoidance of all
rational prime norm divisors at cutoff 29. No primality is asserted. -/
namespace Erdos952Investigation.FullSieve29
open Sieve729
open Sieve729Ten (sqDist sqDist_comm decode embed embed_norm embed_injective embed_step_norm)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def RowAllowed (u : ℤ) : Prop :=
  (2*u+1)%11 ≠ 0 ∧ (2*u+1)%19 ≠ 0 ∧ (2*u+1)%23 ≠ 0

def Good (z : ℤ × ℤ) : Prop := Sieve729.Allowed z ∧ RowAllowed z.1

instance (z : ℤ × ℤ) : Decidable (Good z) :=
  inferInstanceAs (Decidable (Sieve729.Allowed z ∧
    (2*z.1+1)%11 ≠ 0 ∧ (2*z.1+1)%19 ≠ 0 ∧ (2*z.1+1)%23 ≠ 0))

def RowCheck (p : ℕ) : Prop := ∀ a b : Fin p,
  (2*(a : ℤ)+1)%(p : ℤ) ≠ 0 → normPoly a b%(p : ℤ) ≠ 0

lemma row_check_11 : RowCheck 11 := by unfold RowCheck; decide +kernel
lemma row_check_19 : RowCheck 19 := by unfold RowCheck; decide +kernel
lemma row_check_23 : RowCheck 23 := by unfold RowCheck; decide +kernel

lemma norm_nonzero_of_row (p : ℕ) (hp : 0 < p) (hcheck : RowCheck p)
    (u v : ℤ) (hu : (2*u+1)%(p : ℤ) ≠ 0) : normPoly u v%(p : ℤ) ≠ 0 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  let a : Fin p := ⟨(u%(p : ℤ)).toNat,by
    have hh := Int.emod_lt_of_pos u hp'
    omega⟩
  let b : Fin p := ⟨(v%(p : ℤ)).toNat,by
    have hh := Int.emod_lt_of_pos v hp'
    omega⟩
  have ha : (a : ℤ) = u%(p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne')
  have hb : (b : ℤ) = v%(p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne')
  have hh := hcheck a b
  rw [ha,hb,normPoly_mod] at hh
  apply hh
  simpa only [Int.add_emod,Int.mul_emod,Int.emod_emod] using hu

lemma good_full_sieve {z : ℤ × ℤ} (hz : Good z) :
    FiniteSieveReduction.Allowed 29 (embed z) := by
  intro p hpN hp hd
  have hlist : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by
    have hh : ∀ q : Fin 30, q.val.Prime →
        q.val=2 ∨ q.val=3 ∨ q.val=5 ∨ q.val=7 ∨ q.val=11 ∨ q.val=13 ∨
        q.val=17 ∨ q.val=19 ∨ q.val=23 ∨ q.val=29 := by decide +kernel
    exact hh ⟨p,by omega⟩ hp
  have hzero : (embed z).norm%(p : ℤ) = 0 := Int.emod_eq_zero_of_dvd hd
  rcases hlist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (embed z).norm%2 = 0 at hzero
    rw [norm_mod_two] at hzero
    dsimp [embed] at hzero
    omega
  · exact (hz.1 (0 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)
  · exact (hz.1 (1 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)
  · exact (hz.1 (2 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)
  · exact norm_nonzero_of_row 11 (by decide) row_check_11 _ _ hz.2.1 (by simpa only [embed_norm] using hzero)
  · exact (hz.1 (3 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)
  · exact (hz.1 (4 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)
  · exact norm_nonzero_of_row 19 (by decide) row_check_19 _ _ hz.2.2.1 (by simpa only [embed_norm] using hzero)
  · exact norm_nonzero_of_row 23 (by decide) row_check_23 _ _ hz.2.2.2 (by simpa only [embed_norm] using hzero)
  · exact (hz.1 (5 : Fin 6)) (by simpa only [prime,embed_norm] using hzero)

def graph : SimpleGraph (ℤ × ℤ) where
  Adj z w := Good z ∧ Good w ∧ z ≠ w ∧ sqDist z w < 5
  symm := by
    intro z w h
    exact ⟨h.2.1,h.1,h.2.2.1.symm,by rw [← sqDist_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma neighbors_finite (z : ℤ × ℤ) : (graph.neighborSet z).Finite :=
  (Sieve729Ten.neighbors_finite z).subset (fun _ h => ⟨h.1.1,h.2.1.1,h.2.2⟩)

noncomputable instance : graph.LocallyFinite := fun z => (neighbors_finite z).fintype

def check : ℕ → ℕ → (ℤ × ℤ) → (ℤ × ℤ) → Bool
  | 0, _, z, w => decide (z = w ∧ Good z)
  | n+1, code, z, w =>
    let v := z+decode (code%16)
    decide (Good z ∧ z ≠ v ∧ sqDist z v < 5) && check n (code/16) v w

lemma check_sound (n code : ℕ) (z w : ℤ × ℤ) (h : check n code z w = true) :
    Good z ∧ graph.Reachable z w := by
  induction n generalizing code z with
  | zero =>
    have hh : z = w ∧ Good z := by simpa only [check,decide_eq_true_eq] using h
    exact ⟨hh.2,hh.1 ▸ SimpleGraph.Reachable.refl z⟩
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp h
    have hs : Good z ∧ z ≠ z+decode (code%16) ∧
        sqDist z (z+decode (code%16)) < 5 := of_decide_eq_true hh.1
    obtain ⟨hv,hr⟩ := ih (code/16) (z+decode (code%16)) hh.2
    exact ⟨hs.1,(show graph.Adj z (z+decode (code%16)) from
      ⟨hs.1,hv,hs.2.1,hs.2.2⟩).reachable.trans hr⟩

lemma translate_good (k : ℤ) (z : ℤ × ℤ) (hz : Good z) : Good (Sieve729Ten.translate k z) :=
  ⟨Sieve729Ten.translate_allowed k z hz.1,hz.2⟩

lemma reachable_translate (k : ℤ) {z w : ℤ × ℤ} (h : graph.Reachable z w) :
    graph.Reachable (Sieve729Ten.translate k z) (Sieve729Ten.translate k w) := by
  let f : graph →g graph := ⟨Sieve729Ten.translate k,fun {a b} hab =>
    ⟨translate_good k a hab.1,translate_good k b hab.2.1,
      fun he => hab.2.2.1 (Sieve729Ten.translate_injective k he),by
        simpa only [sqDist,Sieve729Ten.translate,add_sub_add_right_eq_sub] using hab.2.2.2⟩⟩
  exact h.map f

lemma infinite_component_of_wrap (h : graph.Reachable (29,0) (29,672945)) :
    {z | graph.Reachable (29,0) z}.Infinite := by
  have hr (n : ℕ) : graph.Reachable (29,0) (Sieve729Ten.translate n (29,0)) := by
    induction n with
    | zero => simpa [Sieve729Ten.translate] using (SimpleGraph.Reachable.refl (29,0) : graph.Reachable _ _)
    | succ n ih =>
      have hh := reachable_translate (n : ℤ) h
      have he : Sieve729Ten.translate (n : ℤ) (29,672945) = Sieve729Ten.translate ((n+1 : ℕ) : ℤ) (29,0) := by
        apply Prod.ext <;> dsimp [Sieve729Ten.translate,period] <;> push_cast <;> ring
      rw [he] at hh
      exact ih.trans hh
  have hi : Function.Injective (fun n : ℕ => Sieve729Ten.translate n (29,0)) := by
    intro i j he
    have hv := congrArg Prod.snd he
    dsimp [Sieve729Ten.translate,period] at hv
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro z ⟨n,rfl⟩
  exact hr n

/-- This is a genuine ordinary-sieve ray at one cutoff, not a prime ray. -/
theorem sieve_ray_of_wrap (h : graph.Reachable (29,0) (29,672945)) :
    FiniteSieveReduction.HasSieveRay 9 29 := by
  obtain ⟨y,_,hy,ha⟩ := (RayReduction.ray_iff_infinite_component graph (29,0)).mpr
    (infinite_component_of_wrap h)
  refine ⟨fun n => embed (y n),embed_injective.comp hy,fun n => good_full_sieve (ha n).1,?_⟩
  intro n
  rw [embed_step_norm]
  have hh := (ha n).2.2.2
  omega

#print axioms good_full_sieve
#print axioms check_sound
#print axioms sieve_ray_of_wrap
end Erdos952Investigation.FullSieve29
