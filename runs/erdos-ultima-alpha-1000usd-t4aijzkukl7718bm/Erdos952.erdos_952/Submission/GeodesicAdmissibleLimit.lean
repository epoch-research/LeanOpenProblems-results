import Submission.GeodesicRayReduction
import Submission.RecurrentAdmissibleReduction

/-!
A prime ray has an admissible translation limit whose increments are uniformly
recurrent and whose nonconsecutive vertices remain separated by the original
jump bound. This is a necessary condition, not a construction of a prime ray
or an obstruction for arbitrary bounds.
-/
namespace Erdos952Investigation.GeodesicAdmissibleLimit
open MinimalWordLimit AdmissibleRay RecurrentAdmissibleReduction
set_option maxHeartbeats 0

/-- Recurrence of the limit upgrades occurrences of its prefixes to arbitrarily
late occurrences in the original word. The original word need not be recurrent. -/
lemma recurrent_prefix_limit_occurs_late {A : Type*} (w v : ℕ → A)
    (hlim : PrefixLimit w v) (hr : UniformlyRecurrent v) (L N : ℕ) :
    ∃ k ≥ N, ∀ i < L, w (k+i) = v i := by
  obtain ⟨R,hR⟩ := hr L
  obtain ⟨n,hn,_,hmatch⟩ := hR N
  obtain ⟨k,hk⟩ := hlim (n+L)
  refine ⟨k+n,by omega,?_⟩
  intro i hi
  simpa only [Nat.add_assoc] using (hk (n+i) (by omega)).trans (hmatch i hi)

/-- There are no short chords between nonconsecutive vertices. -/
def Separated (C : ℤ) (x : ℕ → GaussianInt) : Prop :=
  ∀ i j : ℕ, i+1 < j → C ≤ (x j-x i).norm

lemma separated_of_prime_geodesic (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hd : ∀ i j, (primeGraph C).dist (x i) (x j) = Nat.dist i j) :
    Separated C x := by
  intro i j hij
  by_contra! hs
  have hadj : (primeGraph C).Adj (x i) (x j) :=
    ⟨hp i,hp j,fun he => by have := hx he; omega,hs⟩
  have he := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  rw [hd i j,Nat.dist_eq_sub_of_le (by omega)] at he
  omega

lemma separated_prefix_limit (x y : ℕ → GaussianInt) (C : ℤ)
    (hx : Separated C x)
    (hlim : ∀ L, ∃ k, ∀ i ≤ L, y i = x (k+i)-x k) :
    Separated C y := by
  intro i j hij
  obtain ⟨k,hk⟩ := hlim j
  rw [hk i (by omega),hk j le_rfl]
  have he : (x (k+j)-x k)-(x (k+i)-x k) = x (k+j)-x (k+i) := by abel
  rw [he]
  exact hx _ _ (by omega)

/-- Direct extraction from the prime path retains separation. It does not
retain actual primality. Every finite prefix occurs arbitrarily far out. -/
theorem prime_recurrent_separated_limit (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hs : ∀ n, (increment x n).norm < C) (hsep : Separated C x) :
    ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (increment y n).norm < C) ∧ Separated C y ∧
      (∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) ∧
      UniformlyRecurrent (increment y) ∧
      ∀ L N : ℕ, ∃ k ≥ N, ∀ i ≤ L, y i = x (k+i)-x k := by
  let E := {d : GaussianInt // d.norm < C}
  have hfin : {d : GaussianInt | d.norm < C}.Finite :=
    (norm_sublevel_finite C).subset
      (fun d (hd : d.norm < C) => show d.norm ≤ C from hd.le)
  letI : Finite E := hfin
  let w : ℕ → E := fun n => ⟨increment x n,hs n⟩
  obtain ⟨v,hv,hrec⟩ := uniformly_recurrent_limit w
  let y := integral (fun n => (v n).val)
  have hyinc (n : ℕ) : increment y n = (v n).val := integral_increment _ n
  have hlate (L N : ℕ) : ∃ k ≥ N, ∀ i ≤ L, y i = x (k+i)-x k := by
    obtain ⟨k,hkN,hk⟩ := recurrent_prefix_limit_occurs_late w v hv hrec L N
    refine ⟨k,hkN,integral_block x k L ?_⟩
    intro i hi
    exact congrArg Subtype.val (hk i hi)
  have hprefix (L : ℕ) : ∃ k, ∀ i ≤ L, y i = x (k+i)-x k := by
    obtain ⟨k,_,hk⟩ := hlate L 0
    exact ⟨k,hk⟩
  have hy : Function.Injective y := by
    intro i j he
    obtain ⟨k,hk⟩ := hprefix (max i j)
    rw [hk i (le_max_left _ _),hk j (le_max_right _ _)] at he
    exact Nat.add_left_cancel (hx (sub_left_injective he))
  have hgood (p : ℕ) (hprime : p.Prime) :
      ∃ a b : ZMod p, ∀ n, Good p a b (y n) := by
    letI : NeZero p := ⟨hprime.ne_zero⟩
    obtain ⟨N,hN⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
    have hfinite (L : ℕ) : ∃ ab : ZMod p × ZMod p,
        ∀ i ≤ L, Good p ab.1 ab.2 (y i) := by
      obtain ⟨k,hkN,hk⟩ := hlate L N
      refine ⟨((x k).re,(x k).im),?_⟩
      intro i hi
      rw [hk i hi]
      exact good_of_large_prime (hp (k+i)) hprime (hN _ (by omega))
    obtain ⟨⟨a,b⟩,hab⟩ := finite_choice_prefix
      (fun i (ab : ZMod p × ZMod p) => Good p ab.1 ab.2 (y i)) hfinite
    exact ⟨a,b,hab⟩
  refine ⟨y,integral_zero _,hy,fun n => (hyinc n) ▸ (v n).property,
    separated_prefix_limit x y C hsep hprefix,hgood,?_,hlate⟩
  intro L
  obtain ⟨R,hR⟩ := hrec L
  refine ⟨R,?_⟩
  intro N
  obtain ⟨n,hn,hnR,hmatch⟩ := hR N
  refine ⟨n,hn,hnR,?_⟩
  intro i hi
  rw [hyinc,hyinc,hmatch i hi]

/-- Necessary consequence of the original conjecture. In particular, the
uniform recurrence belongs to an admissible limit, not to an actual prime ray. -/
theorem conjecture_yields_separated_recurrent_admissible
    (h : ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) :
    ∃ (y : ℕ → GaussianInt) (C : ℤ), y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (increment y n).norm < C) ∧ Separated C y ∧
      (∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) ∧
      UniformlyRecurrent (increment y) := by
  obtain ⟨x,C,hx,hp,hd⟩ :=
    GeodesicRayReduction.gaussian_moat_geodesic_equivalence.mp h
  obtain ⟨y,hy0,hy,hs,hsep,hgood,hr,_⟩ := prime_recurrent_separated_limit x C hx
    (fun n => (hp n).1) (fun n => (hp n).2)
    (separated_of_prime_geodesic x C hx (fun n => (hp n).1) hd)
  exact ⟨y,C,hy0,hy,hs,hsep,hgood,hr⟩

#print axioms recurrent_prefix_limit_occurs_late
#print axioms prime_recurrent_separated_limit
#print axioms conjecture_yields_separated_recurrent_admissible
end Erdos952Investigation.GeodesicAdmissibleLimit
