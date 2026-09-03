import Submission.AffineQuadraticSquarefreeSieve

/-!
Local admissibility for simultaneous squarefree binary quadratic values.
These are sieve inputs, not a proof of the cube-Sidon density conjecture.
-/
namespace Erdos1206.QuadraticLocalAdmissibility
open Finset Polynomial QuadraticSquarefreeSieve
open scoped Classical

lemma quadratic_ne_zero {K : Type*} [Field K] {a b c : K}
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    C a*X^2+C b*X+C c ≠ (0 : K[X]) := by
  intro he
  have ha := congrArg (fun f : K[X] => f.coeff 2) he
  have hb := congrArg (fun f : K[X] => f.coeff 1) he
  have hc := congrArg (fun f : K[X] => f.coeff 0) he
  simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C,coeff_zero] at ha hb hc
  norm_num at ha hb hc
  exact h.elim (fun h => h ha) (fun h => h.elim (fun h => h hb) (fun h => h hc))

lemma roots_card {p : ℕ} [NeZero p] (hp : p.Prime) (a b c : ZMod p)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ((univ : Finset (ZMod p)).filter (fun u => a*u^2+b*u+c=0)).card ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : (ZMod p)[X] := C a*X^2+C b*X+C c
  have hf : f ≠ 0 := quadratic_ne_zero h
  have he : (univ : Finset (ZMod p)).filter (fun u => a*u^2+b*u+c=0) =
      f.roots.toFinset := by
    ext x
    simp [Polynomial.mem_roots hf,Polynomial.IsRoot,f]
  rw [he]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' f).trans Polynomial.natDegree_quadratic_le)

/-- More than twice as many residue classes as quadratics suffice when no
quadratic is identically zero. The leading coefficients may vanish. -/
theorem exists_avoiding_residue {r p : ℕ} (hp : p.Prime) (hpr : 2*r < p)
    (a b c : Fin r → ZMod p)
    (h : ∀ i, a i ≠ 0 ∨ b i ≠ 0 ∨ c i ≠ 0) :
    ∃ u : ZMod p, ∀ i, a i*u^2+b i*u+c i ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let R (i : Fin r) := (univ : Finset (ZMod p)).filter
    (fun u => a i*u^2+b i*u+c i=0)
  let B := univ.biUnion R
  have hb : B.card ≤ 2*r := by
    calc
      B.card ≤ ∑ i, (R i).card := card_biUnion_le
      _ ≤ ∑ _ : Fin r, 2 := sum_le_sum (fun i _ => roots_card hp _ _ _ (h i))
      _ = 2*r := by simp [mul_comm]
  have hex : ∃ u : ZMod p, u ∉ B := by
    by_contra! hc
    have hsub : (univ : Finset (ZMod p)) ⊆ B := fun u _ => hc u
    have hh := card_le_card hsub
    have hcard : (univ : Finset (ZMod p)).card = p := by simp
    rw [hcard] at hh
    omega
  obtain ⟨u,hu⟩ := hex
  refine ⟨u,fun i hi => hu ?_⟩
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

lemma square_not_dvd_mul {p d n : ℕ} (hp : p.Prime)
    (hd : Squarefree d) (hn : ¬ p ∣ n) : ¬ p^2 ∣ d*n := by
  intro hh
  have hc : (p^2).Coprime n := (hp.coprime_iff_not_dvd.mpr hn).pow_left 2
  have hpd := hc.dvd_mul_right.mp hh
  exact (Nat.squarefree_iff_prime_squarefree.mp hd p hp) (by simpa [pow_two] using hpd)

/-- Squarefree contents are harmless at a large prime: choose a unit value
for each content-free quadratic. -/
theorem large_prime_locally_squarefree {r p : ℕ} (hp : p.Prime) (hpr : 2*r < p)
    (d a b c : Fin r → ℕ) (hd : ∀ i, Squarefree (d i))
    (h : ∀ i, (a i : ZMod p) ≠ 0 ∨ (b i : ZMod p) ≠ 0 ∨ (c i : ZMod p) ≠ 0) :
    ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ d i*quad (a i) (b i) (c i) t u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u,hu⟩ := exists_avoiding_residue hp hpr
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p)) (fun i => (c i : ZMod p)) h
  refine ⟨1,u.val,fun i => square_not_dvd_mul hp (hd i) ?_⟩
  intro hi
  have hzero := (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hi
  have hh : (a i : ZMod p)*u^2+b i*u+c i=0 := by
    simpa only [quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,
      ZMod.natCast_zmod_val,mul_one,one_mul,one_pow] using hzero
  exact hu i hh


lemma primitive_coefficients_mod_prime {p a b c : ℕ} (hp : p.Prime)
    (h : Nat.gcd a (Nat.gcd b c)=1) :
    (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0 ∨ (c : ZMod p) ≠ 0 := by
  by_contra! hz
  have ha := (CharP.cast_eq_zero_iff (ZMod p) p a).mp hz.1
  have hb := (CharP.cast_eq_zero_iff (ZMod p) p b).mp hz.2.1
  have hc := (CharP.cast_eq_zero_iff (ZMod p) p c).mp hz.2.2
  have hh := Nat.dvd_gcd ha (Nat.dvd_gcd hb hc)
  rw [h] at hh
  exact hp.not_dvd_one hh

lemma quad_scale (d a b c t u : ℕ) :
    quad (d*a) (d*b) (d*c) t u=d*quad a b c t u := by
  dsimp [quad]
  ring

lemma discriminant_scale (d a b c : ℕ) :
    discriminant (d*a) (d*b) (d*c)=(d:ℤ)^2*discriminant a b c := by
  dsimp [discriminant]
  push_cast
  ring

/-- For primitive binary quadratic forms with squarefree positive contents,
only primes at most twice the number of forms need individual local tests.
The density conclusion is for parameters in an affine lattice. -/
theorem small_prime_tests_suffice {r : ℕ} (hr : 0 < r)
    (d a b c : Fin r → ℕ) (hd : ∀ i, 0 < d i ∧ Squarefree (d i))
    (ha : ∀ i, 0 < a i)
    (hprim : ∀ i, Nat.gcd (a i) (Nat.gcd (b i) (c i))=1)
    (hdisc : ∀ i, discriminant (a i) (b i) (c i) ≠ 0)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2*r →
      ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ d i*quad (a i) (b i) (c i) t u) :
    ∃ M v w : ℕ, 0 < M ∧ 0 < w ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (N:ℝ)^2/2 ≤ (AffineQuadraticSquarefreeSieve.goodPairs
        (fun i => d i*a i) (fun i => d i*b i) (fun i => d i*c i) M v w N).card := by
  apply AffineQuadraticSquarefreeSieve.exists_squarefree_progression hr
  · intro i
    exact Nat.mul_pos (hd i).1 (ha i)
  · intro i
    rw [discriminant_scale]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (hd i).1.ne' : (d i:ℤ) ≠ 0)) (hdisc i)
  · intro p hp
    have hl : ∃ t u : ℕ, ∀ i, ¬ p^2 ∣ d i*quad (a i) (b i) (c i) t u := by
      by_cases hpr : p ≤ 2*r
      · exact hsmall p hp hpr
      · exact large_prime_locally_squarefree hp (by omega) d a b c (fun i => (hd i).2)
          (fun i => primitive_coefficients_mod_prime hp (hprim i))
    simpa only [quad_scale] using hl

#print axioms exists_avoiding_residue
#print axioms large_prime_locally_squarefree
#print axioms small_prime_tests_suffice
end Erdos1206.QuadraticLocalAdmissibility
