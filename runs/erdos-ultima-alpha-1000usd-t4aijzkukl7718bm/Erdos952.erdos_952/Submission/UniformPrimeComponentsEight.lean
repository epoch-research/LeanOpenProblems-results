import Submission.UniformPrimeSegmentsEight
import Submission.SievePeriodicDrift

/-! A uniform diameter bound for all actual prime components at squared jump
bound at most eight. This strengthens the existing fixed-bound obstruction;
it does not provide a bound for arbitrary larger jump thresholds. -/
namespace Erdos952Investigation.UniformPrimeComponentsEight
open FinitePrimeSegments SievePeriodicDrift UniformPrimeSegmentsEight
set_option maxHeartbeats 0

lemma walk_vertices_prime {C : ℤ} {z w : GaussianInt}
    (p : (primeGraph C).Walk z w) (hz : Prime z) :
    ∀ i, Prime (p.getVert i) := by
  induction p with
  | nil => simpa using fun _ : ℕ => hz
  | @cons z v w h p ih =>
    intro i
    cases i with
    | zero => simpa using hz
    | succ i => exact ih h.2.1 i

lemma path_length_lt_of_no_segment {C : ℤ} {L : ℕ}
    (hL : ¬ HasPrimeSegment C L) {z w : GaussianInt}
    (hz : Prime z) (p : (primeGraph C).Walk z w) (hp : p.IsPath) :
    p.length < L := by
  by_contra! hn
  apply hL
  refine ⟨p.getVert,?_,?_,?_⟩
  · intro i hi j hj he
    exact hp.getVert_injOn ((Set.mem_Iic.mp hi).trans hn)
      ((Set.mem_Iic.mp hj).trans hn) he
  · intro i _
    exact walk_vertices_prime p hz i
  · intro i hi
    exact (p.adj_getVert_succ (hi.trans_le hn)).2.2.2

lemma walk_taxicab_bound {C : ℤ} {z w : GaussianInt}
    (p : (primeGraph C).Walk z w) :
    taxicab (w-z) ≤ (p.length : ℤ)*C := by
  induction p with
  | nil => simp [taxicab]
  | @cons z v w h p ih =>
    have he : w-z = (w-v)+(v-z) := by abel
    have ht := taxicab_add_le (w-v) (v-z)
    have hs := (taxicab_le_norm (v-z)).trans h.2.2.2.le
    rw [he]
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- One bound works for every starting prime, rather than depending on its
norm or on the location of its component. -/
theorem uniform_component_taxicab_bound (C : ℤ) (hC : C ≤ 8)
    {z w : GaussianInt} (hz : Prime z) (hw : (primeGraph C).Reachable z w) :
    |w.re-z.re|+|w.im-z.im| < 8*(lengthBound : ℤ) := by
  obtain ⟨p,hp⟩ := hw.exists_walk_length_eq_dist
  have hl := path_length_lt_of_no_segment (no_long_prime_segment C hC)
    hz p (p.isPath_of_length_eq_dist hp)
  have ht := walk_taxicab_bound p
  have hm := mul_le_mul_of_nonneg_left hC (Int.natCast_nonneg p.length)
  have hl' : (p.length : ℤ) < lengthBound := by exact_mod_cast hl
  change |w.re-z.re|+|w.im-z.im| ≤ (p.length : ℤ)*C at ht
  nlinarith

/-- The same uniform bound in squared Euclidean displacement. -/
theorem uniform_component_norm_bound (C : ℤ) (hC : C ≤ 8)
    {z w : GaussianInt} (hz : Prime z) (hw : (primeGraph C).Reachable z w) :
    (w-z).norm < (8*(lengthBound : ℤ))^2 := by
  have ht := uniform_component_taxicab_bound C hC hz hw
  have hr := abs_nonneg (w.re-z.re)
  have hi := abs_nonneg (w.im-z.im)
  have hp : (0 : ℤ) < lengthBound := by exact_mod_cast lengthBound_pos
  rw [gaussian_norm_sq]
  change (w.re-z.re)^2+(w.im-z.im)^2 < (8*(lengthBound : ℤ))^2
  nlinarith [sq_abs (w.re-z.re),sq_abs (w.im-z.im),
    mul_nonneg hr hi]

#print axioms uniform_component_taxicab_bound
#print axioms uniform_component_norm_bound
end Erdos952Investigation.UniformPrimeComponentsEight
