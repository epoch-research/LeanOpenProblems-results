import Submission.ColoringReduction
import Submission.CubeCollisionGrowth

/-!
A large-prime-factor source still contains a dilation of every finite set of
positive roots. Its finite-coloring problem is therefore exactly the full
finite-coloring problem. It also has finite induced collision hypergraphs
with arbitrarily large edge/vertex ratio. Neither statement settles the
positive-density Sidon conjecture or bounds independence ratios.
-/

namespace Erdos1206
open Filter
open scoped Topology

/-- Each finite positive prefix has a positive integer dilation into `S`. -/
def HasPrefixDilations (S : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ, 0 < n → n ≤ M → q*n ∈ S

/-- An exact integer-power formulation of `P⁺(n) > n^((k-1)/k)`. -/
def largePrimeSource (k : ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ n^(k-1) < p^k}

lemma prime_mul_mem_largePrimeSource {k p n : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hn : 0 < n) (hpn : n^(k-1) < p) :
    p*n ∈ largePrimeSource k := by
  refine ⟨Nat.mul_pos hp.pos hn, p, hp, dvd_mul_right p n, ?_⟩
  rw [mul_pow]
  have h := Nat.mul_lt_mul_of_pos_left hpn (pow_pos hp.pos (k-1))
  simpa only [← pow_succ, Nat.sub_add_cancel hk] using h

/-- The prime can be larger than any prescribed lower bound. -/
lemma largePrimeSource_prime_prefix (k : ℕ) (hk : 0 < k) (M B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧
      ∀ n : ℕ, 0 < n → n ≤ M → p*n ∈ largePrimeSource k := by
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (max (M^(k-1)) B + 1)
  refine ⟨p, hp, by omega, fun n hn hnM => ?_⟩
  apply prime_mul_mem_largePrimeSource hk hp hn
  exact (Nat.pow_le_pow_left hnM (k-1)).trans_lt (by omega)

lemma largePrimeSource_hasPrefixDilations (k : ℕ) (hk : 0 < k) :
    HasPrefixDilations (largePrimeSource k) := by
  intro M
  obtain ⟨p,hp,_,h⟩ := largePrimeSource_prime_prefix k hk M 0
  exact ⟨p,hp.pos,h⟩

lemma goodCubeColoring_of_prefix_dilations {k : ℕ} {S : Set ℕ} {c : ℕ → Fin k}
    (hS : HasPrefixDilations S)
    (hc : ∀ i, IsSidon ((fun a : ℕ => a^3) ''
      {n | 0 < n ∧ n ∈ S ∧ c n = i})) :
    ∃ d : ℕ → Fin k, GoodCubeColoring d := by
  classical
  choose q hq hqS using hS
  let f : ℕ → ℕ → Fin k := fun M n => c (q M * n)
  obtain ⟨d, φ, hφ, hd⟩ := SeqCompactSpace.tendsto_subseq f
  have hev (n : ℕ) : ∀ᶠ j : ℕ in atTop, f (φ j) n = d n := by
    have hn := (tendsto_pi_nhds.mp hd) n
    exact hn.eventually (isOpen_discrete {d n} |>.mem_nhds (by simp))
  refine ⟨d, ?_⟩
  intro i
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩ heq
  have hlarge : ∀ᶠ j : ℕ in atTop, a + b + r + s ≤ φ j :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop (a + b + r + s))
  obtain ⟨j, hj, hja, hjb, hjr, hjs⟩ :=
    (hlarge.and ((hev a).and ((hev b).and ((hev r).and (hev s))))).exists
  have heq' : (q (φ j) * a)^3 + (q (φ j) * r)^3 =
      (q (φ j) * b)^3 + (q (φ j) * s)^3 := by
    simpa only [mul_pow, ← mul_add] using
      congrArg (fun n : ℕ => q (φ j)^3 * n) heq
  have h := hc i
    _ ⟨q (φ j)*a, ⟨Nat.mul_pos (hq _) ha.1, hqS _ a ha.1 (by omega),
        hja.trans ha.2⟩, rfl⟩
    _ ⟨q (φ j)*b, ⟨Nat.mul_pos (hq _) hb.1, hqS _ b hb.1 (by omega),
        hjb.trans hb.2⟩, rfl⟩
    _ ⟨q (φ j)*r, ⟨Nat.mul_pos (hq _) hr.1, hqS _ r hr.1 (by omega),
        hjr.trans hr.2⟩, rfl⟩
    _ ⟨q (φ j)*s, ⟨Nat.mul_pos (hq _) hs.1, hqS _ s hs.1 (by omega),
        hjs.trans hs.2⟩, rfl⟩ heq'
  simp only [mul_pow] at h
  have hq3 : 0 < q (φ j)^3 := pow_pos (hq _) _
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁, Nat.eq_of_mul_eq_mul_left hq3 h₂⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁, Nat.eq_of_mul_eq_mul_left hq3 h₂⟩

/-- Restricting to this large-prime source does not weaken the existence of
 a coloring with a given finite number of cube-Sidon fibers. -/
theorem largePrimeSource_coloring_iff (r : ℕ) (hr : 0 < r) (k : ℕ) :
    (∃ c : ℕ → Fin k, ∀ i, IsSidon ((fun a : ℕ => a^3) ''
      {n | 0 < n ∧ n ∈ largePrimeSource r ∧ c n = i})) ↔
    (∃ c : ℕ → Fin k, GoodCubeColoring c) := by
  constructor
  · rintro ⟨c,hc⟩
    exact goodCubeColoring_of_prefix_dilations
      (largePrimeSource_hasPrefixDilations r hr) hc
  · rintro ⟨c,hc⟩
    refine ⟨c, fun i => Set.IsSidon.subset (hc i) ?_⟩
    apply Set.image_mono
    exact fun _ hn => ⟨hn.1,hn.2.2⟩

namespace LargePrimeSource
open Finset CubeCollisionGrowth

lemma dilate_injective {q : ℕ} (hq : 0 < q) : Function.Injective (dilate q) := by
  intro x y h
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun z : Quad => z.1) h)
  · apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun z : Quad => z.2.1) h)
    · apply Prod.ext
      · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun z : Quad => z.2.2.1) h)
      · exact Nat.eq_of_mul_eq_mul_left hq (congrArg (fun z : Quad => z.2.2.2) h)

/-- Strict cubic collision on a specified finite vertex set. -/
def EdgeOn (S : Finset ℕ) (x : Quad) : Prop :=
  x.1 ∈ S ∧ x.2.1 ∈ S ∧ x.2.2.1 ∈ S ∧ x.2.2.2 ∈ S ∧
  0 < x.1 ∧ x.1 < x.2.1 ∧ x.2.1 < x.2.2.1 ∧ x.2.2.1 < x.2.2.2 ∧
  x.1^3+x.2.2.2^3=x.2.1^3+x.2.2.1^3

/-- No uniform linear bound can hold on all finite induced subhypergraphs
of a source containing dilations of all positive prefixes. This makes no
claim about the edge count of the source's full natural prefixes. -/
theorem no_hereditary_linear_bound {D : Set ℕ} (hD : HasPrefixDilations D) (C : ℕ) :
    ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ D ∧
      ∃ E : Finset Quad, (∀ x ∈ E, EdgeOn S x) ∧ C*S.card < E.card := by
  classical
  obtain ⟨M,hM⟩ := collision_count_superlinear (C : ℝ)
  obtain ⟨q,hq,hqD⟩ := hD M
  let S := (Icc 1 M).image (fun n => q*n)
  let E := (collisionsUpTo M).image (dilate q)
  have hSmem (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) : q*n ∈ S :=
    mem_image.mpr ⟨n,mem_Icc.mpr ⟨hn,hnM⟩,rfl⟩
  refine ⟨S, ?_, E, ?_, ?_⟩
  · intro n hn
    change n ∈ (Icc 1 M).image (fun m => q*m) at hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    exact hqD m (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    simp only [collisionsUpTo, mem_filter, mem_product, mem_range] at hy
    obtain ⟨⟨haM,hbM,hcM,hdM⟩,ha,hab,hbc,hcd,he⟩ := hy
    refine ⟨hSmem _ ha (by omega), hSmem _ (by omega) (by omega),
      hSmem _ (by omega) (by omega), hSmem _ (by omega) (by omega),
      Nat.mul_pos hq ha, Nat.mul_lt_mul_of_pos_left hab hq,
      Nat.mul_lt_mul_of_pos_left hbc hq, Nat.mul_lt_mul_of_pos_left hcd hq, ?_⟩
    simpa only [dilate, mul_pow, ← mul_add] using congrArg (fun n : ℕ => q^3*n) he
  · have hS : S.card ≤ M := by
      calc
        S.card ≤ (Icc 1 M).card := card_image_le
        _ = M := by simp
    have hE : E.card = (collisionsUpTo M).card :=
      card_image_of_injective _ (dilate_injective hq)
    have hcount : C*M < (collisionsUpTo M).card := by exact_mod_cast hM M le_rfl
    rw [hE]
    exact (Nat.mul_le_mul_left C hS).trans_lt hcount

theorem largePrimeSource_no_hereditary_linear_bound (k : ℕ) (hk : 0 < k) (C : ℕ) :
    ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ largePrimeSource k ∧
      ∃ E : Finset Quad, (∀ x ∈ E, EdgeOn S x) ∧ C*S.card < E.card :=
  no_hereditary_linear_bound (largePrimeSource_hasPrefixDilations k hk) C

end LargePrimeSource

#print axioms largePrimeSource_coloring_iff
#print axioms LargePrimeSource.largePrimeSource_no_hereditary_linear_bound

end Erdos1206
