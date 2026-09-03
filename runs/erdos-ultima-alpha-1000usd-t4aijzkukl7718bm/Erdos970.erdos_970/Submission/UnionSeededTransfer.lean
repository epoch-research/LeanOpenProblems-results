import Submission.UnionReferenceSource
import Submission.SeededEnvelopeBridge

/-! End-to-end use of overlap-aware arithmetic sources in the seeded sieve.
Positivity remains an explicit numerical hypothesis; no uniform quadratic
certificate is asserted. -/
namespace Erdos970.RecursiveSieve
open Finset FiniteSelberg

noncomputable def unionBlockSource {K : ℕ} (p v : Fin K → ℕ)
    (j g : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  let t := unionSourceGain p v (prefixIndices K n) (j n)
  max 0 (t/(g n : ℝ)*(x-1)-t)

/-- Exact union-budget sources and moment errors refer to the same boosted
population at every recursive node. -/
theorem survivor_from_union_sources (K m : ℕ) (p v : Fin K → ℕ)
    (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (hvp : ∀ i, v i ≤ p i) (r : ℕ → ℕ) (j g : ℕ → ℕ)
    (hknown : ∀ n ≤ K, IsJacobsthalBound (j n) (g n) ∧ 0 < g n)
    (hpos : 0 < (seededEnvelope
      (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)-1)
      (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)+1)
      (fun n T => unionBlockSource p v j g n ((m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)))
      K ∅).1) :
    ∃ x < m, ∀ i : Fin K, ¬x ≡ r (p i) [MOD p i] := by
  let q (i : Fin K) : ℝ := 1/(p i : ℝ)
  let q' (i : Fin K) : ℝ := 1/(v i : ℝ)
  let a (i : Fin K) : ℝ := (q' i-q i)/(1-q i)
  let ω (x : ℕ) (i : Fin K) := decide (x ≡ r (p i) [MOD p i])
  have hq (i : Fin K) : q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1 := by
    have hpR : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hvR : (1 : ℝ) < v i := by exact_mod_cast (hv i).one_lt
    refine ⟨(div_lt_one (by linarith : (0 : ℝ) < p i)).mpr hpR,
      one_div_le_one_div_of_le (by linarith) (by exact_mod_cast hvp i),
      (div_le_one (by linarith : (0 : ℝ) < v i)).mpr hvR.le⟩
  have ha (i : Fin K) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hd : 0 < 1-q i := sub_pos.mpr (hq i).1
    refine ⟨div_nonneg (sub_nonneg.mpr (hq i).2.1) hd.le, ?_⟩
    exact (div_le_one hd).mpr (by linarith [(hq i).2.2])
  have hae (i : Fin K) : a i+(1-a i)*q i = q' i := by
    have hn : 1-q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp only [a]
    field_simp
    ring
  let A := (range m) ×ˢ (univ : Finset (Fin K → Bool))
  let w (x : ℕ × (Fin K → Bool)) := probability a x.2
  let Ω (x : ℕ × (Fin K → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact (ha i).1
    · exact sub_nonneg.mpr (ha i).2
  have hmom (T : Finset ℕ) :
      |moment A w Ω T-(m : ℝ)*∏ i ∈ liftSet K T, q' i| ≤ 1 := by
    have hh := added_hits_moment_error a q ha m ω
      (prime_hits_intersection_error p hp hpinj r m) (liftSet K T)
    simpa only [hae,A,w,Ω,boosted_moment] using hh
  have hsource (n : ℕ) (hn : n ≤ K) (T : Finset ℕ) (hT : ∀ i ∈ T, n ≤ i) :
      unionBlockSource p v j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i) ≤ sifted A w Ω T n := by
    have hh := union_reference_cardinality_lower (hknown n hn).1 (hknown n hn).2
      p v hp hv hpinj hvinj hvp r m (liftSet K T) (prefixIndices K n)
      (liftSet_disjoint_prefix K n T hT)
    change unionBlockSource p v j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i) ≤
      sifted (range m ×ˢ univ) (fun x => probability a x.2)
        (fun x => extendPattern (fun i => ω x.1 i || x.2 i)) T n
    rw [boosted_sifted K n m hn]
    simpa only [unionBlockSource,ω,a,q,q'] using hh
  obtain ⟨x,hx,hall⟩ := weighted_survivor_of_positive_seededEnvelope A w Ω hw
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, q' i-1)
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, q' i+1)
    (fun n T => unionBlockSource p v j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i))
    (fun T => by linarith [(abs_le.mp (hmom T)).1])
    (fun T => by linarith [(abs_le.mp (hmom T)).2]) K hsource hpos
  refine ⟨x.1,mem_range.mp (mem_product.mp hx).1,?_⟩
  intro i
  have hh := hall i.val i.isLt
  simp only [Ω,extendPattern,i.isLt,dif_pos] at hh
  have hf := (Bool.or_eq_false_iff.mp hh).1
  exact of_decide_eq_false hf

/-- Scalar-form criterion, still requiring established source bounds and
positive numerical evaluation for the actual/reference pair of prime lists. -/
theorem survivor_from_linear_union_sources (K m : ℕ) (p v : Fin K → ℕ)
    (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (hvp : ∀ i, v i ≤ p i) (r : ℕ → ℕ) (j g : ℕ → ℕ)
    (hknown : ∀ n ≤ K, IsJacobsthalBound (j n) (g n) ∧ 0 < g n)
    (hpos : 0 < (seededLinearEnvelope
      (extendMarginal (fun i => 1/(v i : ℝ))) (unionBlockSource p v j g) K (m : ℝ)).1) :
    ∃ x < m, ∀ i : Fin K, ¬x ≡ r (p i) [MOD p i] := by
  have he := seededLinearEnvelope_eq_seededEnvelope
    (extendMarginal (fun i => 1/(v i : ℝ))) (unionBlockSource p v j g)
    (m : ℝ) K ∅ (by simp)
  simp only [prod_empty,mul_one,prod_extendMarginal] at he
  rw [he] at hpos
  exact survivor_from_union_sources K m p v hp hv hpinj hvinj hvp r j g hknown hpos

#print axioms survivor_from_union_sources
#print axioms survivor_from_linear_union_sources
end Erdos970.RecursiveSieve
