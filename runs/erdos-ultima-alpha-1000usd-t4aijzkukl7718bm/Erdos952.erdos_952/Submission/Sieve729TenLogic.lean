import Submission.Sieve729Application
import Submission.GraphReduction

/-! Certificate checker for a wrapping walk at squared jump bound `< 10` in
one particular six-prime sieve. Passing this sieve does not imply primality. -/
namespace Erdos952Investigation.Sieve729Ten
open Sieve729
set_option maxHeartbeats 0
set_option maxRecDepth 100000

instance (z : ℤ × ℤ) : Decidable (Allowed z) :=
  inferInstanceAs (Decidable (∀ k : Fin 6, normPoly z.1 z.2 % (prime k : ℤ) ≠ 0))

def sqDist (z w : ℤ × ℤ) : ℤ := (w.1-z.1)^2+(w.2-z.2)^2

lemma sqDist_comm (z w : ℤ × ℤ) : sqDist z w = sqDist w z := by
  dsimp [sqDist]
  ring

def graph : SimpleGraph (ℤ × ℤ) where
  Adj z w := Allowed z ∧ Allowed w ∧ z ≠ w ∧ sqDist z w < 5
  symm := by
    intro z w h
    exact ⟨h.2.1,h.1,h.2.2.1.symm,by rw [← sqDist_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma neighbors_finite (z : ℤ × ℤ) : (graph.neighborSet z).Finite := by
  apply ((Set.finite_Icc (z.1-2) (z.1+2)).prod
    (Set.finite_Icc (z.2-2) (z.2+2))).subset
  intro w hw
  have hh := hw.2.2.2
  dsimp only [sqDist] at hh
  change (z.1-2 ≤ w.1 ∧ w.1 ≤ z.1+2) ∧ (z.2-2 ≤ w.2 ∧ w.2 ≤ z.2+2)
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (w.1-z.1),sq_nonneg (w.2-z.2)]

noncomputable instance : graph.LocallyFinite := fun z => (neighbors_finite z).fintype

/-- Twelve nonzero increments, encoded in four bits each. Unused codes are
zero increments, which the checker rejects. -/
def decode : ℕ → ℤ × ℤ
  | 0 => (-2,0) | 1 => (-1,-1) | 2 => (-1,0) | 3 => (-1,1)
  | 4 => (0,-2) | 5 => (0,-1) | 6 => (0,1) | 7 => (0,2)
  | 8 => (1,-1) | 9 => (1,0) | 10 => (1,1) | 11 => (2,0)
  | _ => (0,0)

def check : ℕ → ℕ → (ℤ × ℤ) → (ℤ × ℤ) → Bool
  | 0, _, z, w => decide (z = w ∧ Allowed z)
  | n+1, code, z, w =>
    let v := z+decode (code%16)
    decide (Allowed z ∧ z ≠ v ∧ sqDist z v < 5) && check n (code/16) v w

lemma check_sound (n code : ℕ) (z w : ℤ × ℤ) (h : check n code z w = true) :
    Allowed z ∧ graph.Reachable z w := by
  induction n generalizing code z with
  | zero =>
    have hh : z = w ∧ Allowed z := by simpa only [check,decide_eq_true_eq] using h
    exact ⟨hh.2,hh.1 ▸ SimpleGraph.Reachable.refl z⟩
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp h
    have hs : Allowed z ∧ z ≠ z+decode (code%16) ∧
        sqDist z (z+decode (code%16)) < 5 := of_decide_eq_true hh.1
    obtain ⟨hv,hr⟩ := ih (code/16) (z+decode (code%16)) hh.2
    exact ⟨hs.1,(show graph.Adj z (z+decode (code%16)) from
      ⟨hs.1,hv,hs.2.1,hs.2.2⟩).reachable.trans hr⟩

def translate (k : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1,z.2+k*period)

lemma translate_allowed (k : ℤ) (z : ℤ × ℤ) (hz : Allowed z) :
    Allowed (translate k z) := by
  have hh := allowed_period (-k) (z.2,z.1) (allowed_swap z hz)
  have ht := allowed_swap _ hh
  simpa only [translate,neg_mul,sub_neg_eq_add] using ht

lemma translate_injective (k : ℤ) : Function.Injective (translate k) := by
  intro z w he
  have hr := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  apply Prod.ext
  · exact hr
  · dsimp [translate] at hi
    exact add_right_cancel hi

lemma reachable_translate (k : ℤ) {z w : ℤ × ℤ} (h : graph.Reachable z w) :
    graph.Reachable (translate k z) (translate k w) := by
  let f : graph →g graph := ⟨translate k,fun {a b} hab =>
    ⟨translate_allowed k a hab.1,translate_allowed k b hab.2.1,
      fun he => hab.2.2.1 (translate_injective k he),by
        simpa only [sqDist,translate,add_sub_add_right_eq_sub] using hab.2.2.2⟩⟩
  exact h.map f

lemma infinite_component_of_wrap
    (h : graph.Reachable (0,4) (0,672949)) :
    {z | graph.Reachable (0,4) z}.Infinite := by
  have hr (n : ℕ) : graph.Reachable (0,4) (translate n (0,4)) := by
    induction n with
    | zero => simpa [translate] using (SimpleGraph.Reachable.refl (0,4) : graph.Reachable _ _)
    | succ n ih =>
      have hh := reachable_translate (n : ℤ) h
      have he : translate (n : ℤ) (0,672949) = translate ((n+1 : ℕ) : ℤ) (0,4) := by
        apply Prod.ext <;> dsimp [translate,period] <;> push_cast <;> ring
      rw [he] at hh
      exact ih.trans hh
  have hi : Function.Injective (fun n : ℕ => translate n (0,4)) := by
    intro i j he
    have hv := congrArg Prod.snd he
    dsimp [translate,period] at hv
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro z ⟨n,rfl⟩
  exact hr n

def embed (z : ℤ × ℤ) : GaussianInt := ⟨1+z.1+z.2,z.1-z.2⟩

lemma embed_injective : Function.Injective embed := by
  intro z w he
  have hr := congrArg Zsqrtd.re he
  have hi := congrArg Zsqrtd.im he
  dsimp [embed] at hr hi
  apply Prod.ext <;> omega

lemma embed_norm (z : ℤ × ℤ) : (embed z).norm = normPoly z.1 z.2 := by
  rw [gaussian_norm_sq]
  rfl

lemma embed_step_norm (z w : ℤ × ℤ) : (embed w-embed z).norm = 2*sqDist z w := by
  simp only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,embed,sqDist]
  ring

/-- This conclusion asserts avoidance of exactly six named prime divisors,
not that the vertices are Gaussian primes or pass every finite sieve. -/
theorem six_prime_ray_of_wrap (h : graph.Reachable (0,4) (0,672949)) :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, ((x n).re+(x n).im)%2 = 1 ∧
        (∀ k : Fin 6, (x n).norm % (prime k : ℤ) ≠ 0) ∧
        (x (n+1)-x n).norm < 10 := by
  obtain ⟨y,_,hy,ha⟩ := (RayReduction.ray_iff_infinite_component graph (0,4)).mpr
    (infinite_component_of_wrap h)
  refine ⟨fun n => embed (y n),embed_injective.comp hy,?_⟩
  intro n
  refine ⟨?_,?_,?_⟩
  · dsimp [embed]
    omega
  · intro k
    rw [embed_norm]
    exact (ha n).1 k
  · rw [embed_step_norm]
    have hh := (ha n).2.2.2
    omega

#print axioms check_sound
#print axioms six_prime_ray_of_wrap
end Erdos952Investigation.Sieve729Ten
