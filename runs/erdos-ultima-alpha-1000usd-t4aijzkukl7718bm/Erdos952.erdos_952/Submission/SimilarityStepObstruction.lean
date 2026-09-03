import Submission.NormEightRuns

/-!
The norm-eight finite lift transfers to any four orthogonal directions whose
common Gaussian factor is invertible modulo65. The allowed magnitudes are
unbounded, but the theorem still restricts the set of possible increments.
-/
namespace Erdos952Investigation.SimilarityStepObstruction
open NormEightOnly NormEightRuns
set_option maxHeartbeats 0

def base : GaussianInt := ⟨2,2⟩
lemma base_norm : base.norm = 8 := by norm_num [base,gaussian_norm_sq]
lemma base_ne_zero : base ≠ 0 := by decide

lemma allowed_iff_norm (z : GaussianInt) :
    Allowed (residue z.re) (residue z.im) ↔ z.norm%5 ≠ 0 ∧ z.norm%13 ≠ 0 := by
  unfold Allowed
  rw [norm_mod_residue _ _ _ (by norm_num : (5 : ℤ) ∣ 65),
    norm_mod_residue _ _ _ (by norm_num : (13 : ℤ) ∣ 65),← gaussian_norm_sq]

lemma norm_add_period (z w : GaussianInt) :
    (z+65*w).norm ≡ z.norm [ZMOD 65] := by
  have hr : (z+65*w).re ≡ z.re [ZMOD 65] := by
    simp only [Zsqrtd.re_add,Zsqrtd.re_mul,Zsqrtd.re_ofNat,Zsqrtd.im_ofNat,
      mul_zero,zero_mul,add_zero]
    change (z.re+65*w.re)%65 = z.re%65
    omega
  have hi : (z+65*w).im ≡ z.im [ZMOD 65] := by
    simp only [Zsqrtd.im_add,Zsqrtd.im_mul,Zsqrtd.re_ofNat,Zsqrtd.im_ofNat,
      mul_zero,zero_mul,add_zero]
    change (z.im+65*w.im)%65 = z.im%65
    omega
  simpa only [gaussian_norm_sq] using (hr.pow 2).add (hi.pow 2)

lemma allowed_of_scaled_norm_congruence (g x y : GaussianInt)
    (hx : Allowed (residue x.re) (residue x.im))
    (hc : g.norm*y.norm ≡ 8*x.norm [ZMOD 65]) :
    Allowed (residue y.re) (residue y.im) := by
  rw [allowed_iff_norm] at hx ⊢
  constructor
  · intro hy
    have he := hc.of_dvd (by norm_num : (5 : ℤ) ∣ 65)
    change (g.norm*y.norm)%5 = (8*x.norm)%5 at he
    rw [Int.mul_emod g.norm y.norm 5,hy,mul_zero] at he
    have hh := hx.1
    omega
  · intro hy
    have he := hc.of_dvd (by norm_num : (13 : ℤ) ∣ 65)
    change (g.norm*y.norm)%13 = (8*x.norm)%13 at he
    rw [Int.mul_emod g.norm y.norm 13,hy,mul_zero] at he
    have hh := hx.2
    omega

/-- Similarity is used only to transport a sieve condition; it is not asserted
to preserve primality. -/
theorem no_unit_multiple_allowed_segment (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Set.InjOn x (Set.Iic 4225))
    (ha : ∀ n ≤ 4225, Allowed (residue (x n).re) (residue (x n).im)) :
    ¬ ∀ n < 4225, ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  intro hs
  have ht (n : ℕ) : ∃ e : GaussianInt, e.norm = 1 ∧
      (n < 4225 → x (n+1)-x n = g*e) := by
    by_cases hn : n < 4225
    · obtain ⟨e,he,hd⟩ := hs n hn
      exact ⟨e,he,fun _ => hd⟩
    · exact ⟨1,by norm_num [gaussian_norm_sq],fun hh => (hn hh).elim⟩
  choose e he hstep using ht
  obtain ⟨a,b,hab⟩ := hg
  let q (n : ℕ) : GaussianInt := ∑ i ∈ Finset.range n, e i
  have hq0 : q 0 = 0 := by simp [q]
  have hqS (n : ℕ) : q (n+1) = q n+e n := by simp [q,Finset.sum_range_succ]
  have hform (n : ℕ) (hn : n ≤ 4225) : x n = x 0+g*q n := by
    induction n with
    | zero => rw [hq0]; ring
    | succ n ih =>
      calc
        x (n+1) = x n+g*e n := by linear_combination hstep n (by omega)
        _ = x 0+g*q (n+1) := by rw [ih (by omega),hqS]; ring
  let r : GaussianInt := (a : GaussianInt)*star g*base*x 0
  let y (n : ℕ) : GaussianInt := r+base*q n
  have hrel (n : ℕ) (hn : n ≤ 4225) : g*y n = base*x n+65*(-(b : GaussianInt)*base*x 0) := by
    have ht : (a : GaussianInt)*(g.norm : GaussianInt)+(b : GaussianInt)*65 = 1 := by
      exact_mod_cast hab
    rw [Zsqrtd.norm_eq_mul_conj] at ht
    dsimp only [y,r]
    rw [hform n hn]
    linear_combination (base*x 0)*ht
  have hnrel (n : ℕ) (hn : n ≤ 4225) : g.norm*(y n).norm ≡ 8*(x n).norm [ZMOD 65] := by
    have hh := norm_add_period (base*x n) (-(b : GaussianInt)*base*x 0)
    rw [← hrel n hn,Zsqrtd.norm_mul,Zsqrtd.norm_mul,base_norm] at hh
    exact hh
  have hy : Set.InjOn y (Set.Iic 4225) := by
    intro i hi j hj hij
    change r+base*q i = r+base*q j at hij
    have hq := mul_left_cancel₀ base_ne_zero (add_left_cancel hij)
    apply hx hi hj
    rw [hform i hi,hform j hj,hq]
  have hyS (n : ℕ) : (y (n+1)-y n).norm = 8 := by
    have hh : y (n+1)-y n = base*e n := by
      dsimp only [y]
      rw [hqS]
      ring
    rw [hh,Zsqrtd.norm_mul,base_norm,he n,mul_one]
  apply no_long_allowed_segment y hy
    (fun n hn => allowed_of_scaled_norm_congruence g (x n) (y n) (ha n hn) (hnrel n hn))
  exact fun n _ => hyS n

/-- The corresponding infinite-ray obstruction. -/
theorem no_unit_multiple_allowed_ray (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (ha : ∀ n, Allowed (residue (x n).re) (residue (x n).im)) :
    ¬ ∀ n, ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  intro hs
  exact no_unit_multiple_allowed_segment g hg x hx.injOn (fun n _ => ha n)
    (fun n _ => hs n)

/-- The starting index and the run-length bound are uniform over all invertible
similarity factors. This still permits switching between different factors. -/
theorem similar_step_runs_eventually_break (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∃ K : ℕ, ∀ g : GaussianInt, IsCoprime g.norm 65 → ∀ N ≥ K,
      ∃ n, N ≤ n ∧ n < N+4225 ∧
        ¬ ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx 169
  refine ⟨K,?_⟩
  intro g hg N hN
  by_contra! hnone
  apply no_unit_multiple_allowed_segment g hg (fun i => x (N+i))
    (fun _ _ _ _ he => Nat.add_left_cancel (hx he))
    (fun i _ => prime_allowed (hp (N+i)) (hK _ (by omega)))
  intro i hi
  simpa only [Nat.add_assoc] using hnone (N+i) (by omega) (by omega)

/-- An unbounded family of step magnitudes is excluded, provided all steps
are unit multiples of the same factor invertible modulo65. -/
theorem no_unit_multiple_prime_ray (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, ∃ e : GaussianInt, e.norm = 1 ∧ x (n+1)-x n = g*e := by
  intro hs
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx 169
  let y : ℕ → GaussianInt := fun n => x (K+n)
  apply no_unit_multiple_allowed_ray g hg y
    (fun i j he => Nat.add_left_cancel (hx he))
    (fun n => prime_allowed (hp (K+n)) (hK _ (by omega)))
  intro n
  simpa only [y,Nat.add_assoc] using hs (K+n)

def imagUnit : GaussianInt := ⟨0,1⟩

/-- Explicitly, arbitrary signs and arbitrary switches between the two
orthogonal directions are allowed. -/
theorem no_four_orthogonal_prime_ray (g : GaussianInt) (hg : IsCoprime g.norm 65)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = g ∨ x (n+1)-x n = -g ∨
      x (n+1)-x n = g*imagUnit ∨ x (n+1)-x n = -(g*imagUnit) := by
  intro hs
  apply no_unit_multiple_prime_ray g hg x hx hp
  intro n
  rcases hs n with h | h | h | h
  · exact ⟨1,by norm_num [gaussian_norm_sq],by simpa using h⟩
  · exact ⟨-1,by norm_num [gaussian_norm_sq],by simpa using h⟩
  · exact ⟨imagUnit,by norm_num [imagUnit,gaussian_norm_sq],h⟩
  · exact ⟨-imagUnit,by norm_num [imagUnit,gaussian_norm_sq],by simpa using h⟩

#print axioms no_unit_multiple_allowed_segment
#print axioms similar_step_runs_eventually_break
#print axioms no_unit_multiple_allowed_ray
#print axioms no_unit_multiple_prime_ray
#print axioms no_four_orthogonal_prime_ray
end Erdos952Investigation.SimilarityStepObstruction
