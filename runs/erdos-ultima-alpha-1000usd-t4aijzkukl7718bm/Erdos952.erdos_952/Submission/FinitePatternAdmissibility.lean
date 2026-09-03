import Submission.FiniteSieveReduction

/-! A finite configuration with k vertices has no local translation obstruction
at primes larger than k. This gives a finite test for admissibility, not a test
for the existence of an actual Gaussian-prime translate or an infinite ray. -/
namespace Erdos952Investigation.FinitePatternAdmissibility
open AdmissibleRay FiniteSieveReduction
set_option maxHeartbeats 0

lemma exists_avoiding_values {ι K : Type*} [Fintype ι] [Fintype K]
    (hcard : Fintype.card ι < Fintype.card K) (f : ι → K) :
    ∃ a : K, ∀ i, a ≠ f i := by
  classical
  by_contra! h
  have hf : Function.Surjective f := fun a => by
    obtain ⟨i,hi⟩ := h a
    exact ⟨i,hi.symm⟩
  have hh := Fintype.card_le_of_surjective f hf
  omega

/-- Over a finite field, fewer than |K| points cannot obstruct all translates
of the nonzero sum-of-two-squares locus. -/
theorem finite_field_translate {ι K : Type*} [Fintype ι] [Fintype K] [Field K]
    (hcard : Fintype.card ι < Fintype.card K) (u v : ι → K) :
    ∃ a b : K, ∀ i, (a+u i)^2+(b+v i)^2 ≠ 0 := by
  classical
  by_cases hs : ∃ r : K, r^2 = -1
  · obtain ⟨r,hr⟩ := hs
    obtain ⟨A,hA⟩ := exists_avoiding_values hcard (fun i => -u i+r*v i)
    have hminus (i : ι) : A+u i-r*v i ≠ 0 := by
      intro he
      apply hA i
      linear_combination he
    have hfactor (a b : K) (i : ι) :
        (a+u i)^2+(b+v i)^2 =
          (a+u i-r*(b+v i))*(a+u i+r*(b+v i)) := by
      linear_combination (b+v i)^2*hr
    by_cases h2r : (2 : K)*r = 0
    · refine ⟨A,0,fun i => ?_⟩
      rw [hfactor]
      have he : A+u i+r*v i = A+u i-r*v i := by
        linear_combination v i*h2r
      simpa only [zero_add,he] using mul_ne_zero (hminus i) (hminus i)
    · obtain ⟨B,hB⟩ := exists_avoiding_values hcard (fun i => -u i-r*v i)
      let b : K := (B-A)/(2*r)
      have hb : (2*r)*b = B-A := by
        dsimp [b]
        exact mul_div_cancel₀ _ h2r
      refine ⟨A+r*b,b,fun i => ?_⟩
      rw [hfactor]
      have hm : A+r*b+u i-r*(b+v i) = A+u i-r*v i := by ring
      have hp : A+r*b+u i+r*(b+v i) = B+u i+r*v i := by
        linear_combination hb
      rw [hm,hp]
      apply mul_ne_zero (hminus i)
      intro he
      apply hB i
      linear_combination he
  · obtain ⟨A,hA⟩ := exists_avoiding_values hcard (fun i => -u i)
    refine ⟨A,0,fun i he => ?_⟩
    simp only [zero_add] at he
    by_cases hv : v i = 0
    · have ha : A+u i = 0 := by
        apply sq_eq_zero_iff.mp
        simpa only [hv,zero_pow (by decide : 2 ≠ 0),add_zero] using he
      apply hA i
      linear_combination ha
    · apply hs
      refine ⟨(A+u i)/v i,?_⟩
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hv)).mpr
      linear_combination he

/-- The bound is in the number of vertices, not in the sizes of their
coordinates or the path's jump bound. -/
theorem translate_at_large_prime {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) {p : ℕ} (hp : p.Prime)
    (hk : Fintype.card ι < p) :
    ∃ a b : ZMod p, ∀ i, Good p a b (z i) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact finite_field_translate (by simpa using hk)
    (fun i => ((z i).re : ZMod p)) (fun i => ((z i).im : ZMod p))

def FiniteAdmissible {ι : Type*} (z : ι → GaussianInt) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ i, Good p a b (z i)

theorem finite_admissible_iff_small_primes {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) :
    FiniteAdmissible z ↔ ∀ p ≤ Fintype.card ι, p.Prime →
      ∃ a b : ZMod p, ∀ i, Good p a b (z i) := by
  constructor
  · exact fun h p _ hp => h p hp
  · intro h p hp
    by_cases hk : p ≤ Fintype.card ι
    · exact h p hk hp
    · exact translate_at_large_prime z hp (by omega)

instance goodDecidable (p : ℕ) (a b : ZMod p) (z : GaussianInt) :
    Decidable (Good p a b z) := inferInstanceAs (Decidable (_ ≠ _))

/-- A single local test is finite when p is prime; nonprimes are skipped. -/
def localTest {k : ℕ} (z : Fin k → GaussianInt) (p : ℕ) : Bool :=
  if hp : p.Prime then
    letI : NeZero p := ⟨hp.ne_zero⟩
    decide (∃ a b : ZMod p, ∀ i, Good p a b (z i))
  else true

lemma localTest_true_iff {k : ℕ} (z : Fin k → GaussianInt) (p : ℕ) :
    localTest z p = true ↔
      (p.Prime → ∃ a b : ZMod p, ∀ i, Good p a b (z i)) := by
  by_cases hp : p.Prime <;> simp [localTest,hp]

def admissibilityTest {k : ℕ} (z : Fin k → GaussianInt) : Bool :=
  (List.range (k+1)).all (localTest z)

theorem admissibilityTest_true_iff {k : ℕ} (z : Fin k → GaussianInt) :
    admissibilityTest z = true ↔ FiniteAdmissible z := by
  rw [finite_admissible_iff_small_primes]
  simp only [admissibilityTest,List.all_eq_true,List.mem_range,
    localTest_true_iff,Fintype.card_fin,Nat.lt_succ_iff]

/-- Admissibility only produces translates in each finite sieve. It does not
produce a translate all of whose vertices are prime. -/
theorem admissible_iff_sieve_translates {ι : Type*} (z : ι → GaussianInt) :
    FiniteAdmissible z ↔ ∀ N : ℕ, ∃ t : GaussianInt,
      ∀ i, Allowed N (t+z i) := by
  classical
  constructor
  · intro h N
    choose a b hab using h
    obtain ⟨A,hA⟩ := prime_crt N a
    obtain ⟨B,hB⟩ := prime_crt N b
    refine ⟨⟨A,B⟩,fun i p hpN hp hdiv => ?_⟩
    have hg := hab p hp i
    rw [← hA p hpN hp,← hB p hpN hp] at hg
    apply hg
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (⟨A,B⟩+z i).norm p).mpr hdiv
    simpa [gaussian_norm_sq] using he
  · intro h p hp
    obtain ⟨t,ht⟩ := h p
    refine ⟨t.re,t.im,fun i he => ?_⟩
    apply ht i p le_rfl hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (t+z i).norm p).mp
    simpa [Good,gaussian_norm_sq] using he

example : admissibilityTest (fun i : Fin 2 => (i.val : GaussianInt)) = false := by
  decide +kernel

example : admissibilityTest
    (fun i : Fin 2 => (i.val : GaussianInt)*(⟨1,1⟩ : GaussianInt)) = true := by
  decide +kernel

example : admissibilityTest (fun i : Fin 5 => (2*i.val : GaussianInt)) = false := by
  decide +kernel

#print axioms translate_at_large_prime
#print axioms finite_admissible_iff_small_primes
#print axioms admissibilityTest_true_iff

/-- An obstructed finite configuration can have only finitely many actual
prime translates. Small prime exceptions are retained, rather than discarded. -/
theorem prime_translates_finite_of_not_admissible {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hbad : ¬ FiniteAdmissible z) :
    {t : GaussianInt | ∀ i, Prime (t+z i)}.Finite := by
  classical
  have hn : ¬ ∀ p ≤ Fintype.card ι, p.Prime →
      ∃ a b : ZMod p, ∀ i, Good p a b (z i) := by
    intro h
    exact hbad ((finite_admissible_iff_small_primes z).mpr h)
  push_neg at hn
  obtain ⟨p,_,hp,hpbad⟩ := hn
  let S : Set GaussianInt := ⋃ i : ι,
    (fun w : GaussianInt => w-z i) '' {w : GaussianInt | w.norm ≤ (p : ℤ)^2}
  have hS : S.Finite := Set.finite_iUnion
    (fun i => (norm_sublevel_finite ((p : ℤ)^2)).image (fun w => w-z i))
  apply hS.subset
  intro t ht
  obtain ⟨i,hi⟩ := hpbad t.re t.im
  have he : (t.re+(z i).re : ZMod p)^2+(t.im+(z i).im : ZMod p)^2 = 0 :=
    not_not.mp hi
  have hd : (p : ℤ) ∣ (t+z i).norm := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (t+z i).norm p).mp
    simpa [gaussian_norm_sq] using he
  have hnorm := prime_norm_divisor_bound (ht i) hp hd
  apply Set.mem_iUnion.mpr
  exact ⟨i,⟨t+z i,hnorm,by simp⟩⟩

/-- Infinitely many actual prime translates require passing the finite test.
The converse is not asserted. -/
theorem admissible_of_infinitely_many_prime_translates {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (h : {t : GaussianInt | ∀ i, Prime (t+z i)}.Infinite) :
    FiniteAdmissible z := by
  by_contra hn
  exact h (prime_translates_finite_of_not_admissible z hn)

/-- For every fixed window size, all sufficiently late windows of an
injective prime sequence pass the full finite admissibility test. The tail
index may depend on the size; this is not a uniform bound on path lengths. -/
theorem prime_windows_eventually_test_true (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N,
      admissibilityTest (fun i : Fin k => x (n+i.val)-x n) = true := by
  obtain ⟨N,hN⟩ := injective_escapes_norm x hx ((k : ℤ)^2)
  refine ⟨N,fun n hn => ?_⟩
  apply (admissibilityTest_true_iff _).mpr
  apply (finite_admissible_iff_small_primes _).mpr
  intro p hpk hprime
  refine ⟨(x n).re,(x n).im,fun i => ?_⟩
  apply good_of_large_prime (hp (n+i.val)) hprime
  have hlarge := hN (n+i.val) (by omega)
  have hpk' : (p : ℤ) ≤ k := by simpa using (show (p : ℤ) ≤ (Fintype.card (Fin k) : ℤ) by exact_mod_cast hpk)
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  nlinarith

#print axioms prime_translates_finite_of_not_admissible
#print axioms admissible_of_infinitely_many_prime_translates
#print axioms prime_windows_eventually_test_true

#print axioms admissible_iff_sieve_translates
end Erdos952Investigation.FinitePatternAdmissibility
