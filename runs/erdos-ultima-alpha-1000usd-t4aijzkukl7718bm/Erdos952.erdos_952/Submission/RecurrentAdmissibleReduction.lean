import Submission.MinimalWordLimit
import Submission.FiniteSieveReduction
import Submission.RecurrentIncrementObstruction

/-! Every admissible bounded-step ray has an admissible limit ray with
uniformly recurrent increments. Actual primality is not inherited under
translation limits. This does not prove that such admissible rays exist. -/
namespace Erdos952Investigation
namespace RecurrentAdmissibleReduction
open MinimalWordLimit AdmissibleRay FiniteSieveReduction
set_option maxHeartbeats 0

abbrev increment (x : ℕ → GaussianInt) (n : ℕ) := x (n+1)-x n

def integral (w : ℕ → GaussianInt) (n : ℕ) : GaussianInt :=
  ∑ i ∈ Finset.range n, w i

lemma integral_zero (w : ℕ → GaussianInt) : integral w 0 = 0 := by simp [integral]

lemma integral_succ (w : ℕ → GaussianInt) (n : ℕ) :
    integral w (n+1) = integral w n+w n := by simp [integral,Finset.sum_range_succ]

lemma integral_increment (w : ℕ → GaussianInt) (n : ℕ) :
    increment (integral w) n = w n := by simp [increment,integral_succ]

lemma integral_block {w : ℕ → GaussianInt} (x : ℕ → GaussianInt) (k L : ℕ)
    (he : ∀ i < L, increment x (k+i) = w i) :
    ∀ i ≤ L, integral w i = x (k+i)-x k := by
  intro i
  induction i with
  | zero => intro _; simp [integral_zero]
  | succ i ih =>
    intro hi
    rw [integral_succ,ih (by omega),← he i (by omega)]
    dsimp [increment]
    rw [Nat.add_assoc]
    abel

lemma good_sub_translate {p : ℕ} (a b : ZMod p) (z t : GaussianInt)
    (h : Good p a b z) : Good p (a+t.re) (b+t.im) (z-t) := by
  simpa only [Good,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub,add_add_sub_cancel] using h

/-- Finite-prefix translation limits preserve admissibility and injectivity. -/
lemma admissible_prefix_limit (x y : ℕ → GaussianInt)
    (hx : Function.Injective x)
    (hg : ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n))
    (hprefix : ∀ L : ℕ, ∃ k : ℕ, ∀ i ≤ L, y i = x (k+i)-x k) :
    Function.Injective y ∧
      ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n) := by
  constructor
  · intro i j hij
    obtain ⟨k,hk⟩ := hprefix (max i j)
    rw [hk i (le_max_left _ _),hk j (le_max_right _ _)] at hij
    exact Nat.add_left_cancel (hx (sub_left_injective hij))
  · intro p hp
    letI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨a,b,hab⟩ := hg p hp
    have hfinite : ∀ L : ℕ, ∃ ab : ZMod p × ZMod p,
        ∀ i ≤ L, Good p ab.1 ab.2 (y i) := by
      intro L
      obtain ⟨k,hk⟩ := hprefix L
      refine ⟨(a+(x k).re,b+(x k).im),?_⟩
      intro i hi
      rw [hk i hi]
      exact good_sub_translate a b _ _ (hab (k+i))
    obtain ⟨⟨c,d⟩,hcd⟩ := finite_choice_prefix
      (fun i (ab : ZMod p × ZMod p) => Good p ab.1 ab.2 (y i)) hfinite
    exact ⟨c,d,hcd⟩

/-- The admissible ray in this conclusion is a translated-block limit, not
necessarily a translate or tail of the original ray. -/
theorem uniformly_recurrent_admissible_limit (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hs : ∀ n, (increment x n).norm < C)
    (hg : ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (x n)) :
    ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (increment y n).norm < C) ∧
      (∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) ∧
      UniformlyRecurrent (increment y) ∧
      ∀ L : ℕ, ∃ k : ℕ, ∀ i ≤ L, y i = x (k+i)-x k := by
  let E := {d : GaussianInt // d.norm < C}
  have hfin : {d : GaussianInt | d.norm < C}.Finite :=
    (norm_sublevel_finite C).subset (fun d (hd : d.norm < C) => show d.norm ≤ C from hd.le)
  letI : Finite E := hfin
  let w : ℕ → E := fun n => ⟨increment x n,hs n⟩
  obtain ⟨v,hv,hrec⟩ := uniformly_recurrent_limit w
  let y := integral (fun n => (v n).val)
  have hyinc (n : ℕ) : increment y n = (v n).val := integral_increment _ n
  have hprefix : ∀ L : ℕ, ∃ k : ℕ, ∀ i ≤ L, y i = x (k+i)-x k := by
    intro L
    obtain ⟨k,hk⟩ := hv L
    refine ⟨k,integral_block x k L ?_⟩
    intro i hi
    exact congrArg Subtype.val (hk i hi)
  obtain ⟨hyi,hyg⟩ := admissible_prefix_limit x y hx hg hprefix
  refine ⟨y,integral_zero _,hyi,fun n => (hyinc n) ▸ (v n).property,hyg,?_,hprefix⟩
  intro L
  obtain ⟨R,hR⟩ := hrec L
  refine ⟨R,?_⟩
  intro N
  obtain ⟨n,hn,hnR,hmatch⟩ := hR N
  refine ⟨n,hn,hnR,?_⟩
  intro i hi
  rw [hyinc,hyinc,hmatch i hi]

/-- An exact recurrence reformulation of the admissible-ray condition.
Neither side is established for any sufficiently large fixed bound. -/
theorem admissible_ray_iff_uniformly_recurrent (C : ℤ) :
    HasAdmissibleRay C ↔
      ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
        (∀ n, (increment y n).norm < C) ∧
        (∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) ∧
        UniformlyRecurrent (increment y) := by
  constructor
  · rintro ⟨x,_,hx,hs,hg⟩
    obtain ⟨y,hy0,hy,hyS,hyG,hyR,_⟩ := uniformly_recurrent_admissible_limit x C hx hs hg
    exact ⟨y,hy0,hy,hyS,hyG,hyR⟩
  · rintro ⟨y,hy0,hy,hs,hg,_⟩
    exact ⟨y,hy0,hy,hs,hg⟩

/-- A prime ray would have an admissible uniformly recurrent limit ray. -/
theorem prime_ray_yields_uniformly_recurrent_admissible_ray
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (increment x n).norm < C) :
    ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (increment y n).norm < C) ∧
      (∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) ∧
      UniformlyRecurrent (increment y) :=
  (admissible_ray_iff_uniformly_recurrent C).mp (prime_walk_yields_admissible_ray x C hx h)

lemma uniformly_recurrent_tail {A : Type*} (w : ℕ → A) (hw : UniformlyRecurrent w)
    (K : ℕ) : UniformlyRecurrent (fun n => w (K+n)) := by
  intro L
  obtain ⟨R,hR⟩ := hw (K+L)
  refine ⟨R,?_⟩
  intro N
  obtain ⟨n,hn,hnR,hmatch⟩ := hR N
  refine ⟨n,hn,hnR,?_⟩
  intro i hi
  have hh := hmatch (K+i) (by omega)
  simpa only [Nat.add_left_comm] using hh

/-- Uniformly recurrent limit rays cannot themselves be translated into
actual Gaussian-prime rays, even after deleting an initial segment. -/
theorem no_prime_translate_of_recurrent_limit (y : ℕ → GaussianInt)
    (hy : Function.Injective y) (hr : UniformlyRecurrent (increment y))
    (z : GaussianInt) (K : ℕ) : ¬ ∀ n, Prime (z+y (K+n)) := by
  intro hp
  let x : ℕ → GaussianInt := fun n => z+y (K+n)
  have hx : Function.Injective x := by
    intro i j he
    exact Nat.add_left_cancel (hy (add_left_cancel he))
  have hxi (n : ℕ) : increment x n = increment y (K+n) := by
    simp [increment,x,Nat.add_assoc]
  apply RecurrentIncrementObstruction.prime_increments_not_recurrent x hx hp
  intro L N
  obtain ⟨R,hR⟩ := uniformly_recurrent_tail (increment y) hr K L
  obtain ⟨n,hn,_,hmatch⟩ := hR N
  refine ⟨n,hn,?_⟩
  intro i hi
  change increment x (n+i) = increment x i
  rw [hxi,hxi]
  exact hmatch i hi

#print axioms uniformly_recurrent_admissible_limit
#print axioms admissible_ray_iff_uniformly_recurrent
#print axioms prime_ray_yields_uniformly_recurrent_admissible_ray
#print axioms no_prime_translate_of_recurrent_limit
end RecurrentAdmissibleReduction
end Erdos952Investigation
