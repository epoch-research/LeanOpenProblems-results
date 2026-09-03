import Submission.RationalStripObstruction
import Submission.GraphReduction

/-! Arbitrarily large isolated Gaussian primes at every prescribed finite step
bound. The isolated prime varies with the bound, so this does not settle the
Gaussian moat conjecture. -/
namespace Erdos952Investigation
namespace IsolatedGaussianPrimes
open RationalStrip

set_option maxHeartbeats 0

lemma unit_residue (t : ℕ) (z : GaussianInt)
    (hc : z.norm.natAbs.Coprime (t^2 + 1)) :
    IsUnit (((t : ℤ)*z.im - z.re : ℤ) : ZMod (t^2 + 1)) := by
  let m := t^2 + 1
  have ht : (t : ZMod m)^2 + 1 = 0 := by
    change ((t : ℕ) : ZMod (t^2+1))^2 + 1 = 0
    norm_cast
    exact ZMod.natCast_self (t^2+1)
  have hu : IsUnit ((z.norm : ℤ) : ZMod m) := by
    have hh := (ZMod.isUnit_iff_coprime z.norm.natAbs m).mpr hc
    simpa using hh
  have he : ((((t : ℤ)*z.im - z.re : ℤ) : ZMod m)) *
      (((t : ℤ)*z.im + z.re : ℤ) : ZMod m) = -((z.norm : ℤ) : ZMod m) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_add,
      gaussian_norm_sq, Int.cast_pow]
    linear_combination (z.im : ZMod m)^2 * ht
  exact isUnit_of_mul_isUnit_left (he.symm ▸ hu.neg)

lemma coprime_of_modEq {a b m : ℕ} (h : a ≡ b [MOD m]) (hb : b.Coprime m) :
    a.Coprime m := by
  have he : (a : ZMod m) = (b : ZMod m) := (ZMod.natCast_eq_natCast_iff a b m).mpr h
  apply (ZMod.isUnit_iff_coprime a m).mp
  rw [he]
  exact (ZMod.isUnit_iff_coprime b m).mpr hb

lemma prime_with_prescribed_nonprime_offsets {ι : Type*} [Fintype ι]
    (f : ι → GaussianInt) (hf : ∀ i, f i ≠ 0) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ Prime (p : GaussianInt) ∧
      ∀ i, ¬ Prime ((p : GaussianInt) + f i) := by
  classical
  let B : ℕ := 4 * ∏ i, (f i).norm.natAbs
  have hfn (i : ι) : 0 < (f i).norm.natAbs :=
    Int.natAbs_pos.mpr (GaussianInt.norm_pos.mpr (hf i)).ne'
  have hB : 0 < B := Nat.mul_pos (by decide) (Finset.prod_pos fun i _ => hfn i)
  have h4B : 4 ∣ B := dvd_mul_right _ _
  have hnormB (i : ι) : (f i).norm.natAbs ∣ B :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin ι).injective
  let t : ι → ℕ := fun i => euclidT B (e i)
  let m : ι → ℕ := fun i => euclidM B (e i)
  have hm (i : ι) : m i = t i^2 + 1 := rfl
  have hmpos (i : ι) : 0 < m i := by rw [hm]; positivity
  have hmone (i : ι) : 1 < m i := by
    have ht := t_pos hB (e i)
    change 1 < euclidT B (e i)^2 + 1
    nlinarith
  have hmB (i : ι) : (m i).Coprime B := coprime_m_base B (e i)
  have hm4 (i : ι) : (m i).Coprime 4 := (hmB i).of_dvd_right h4B
  have hmnorm (i : ι) : (f i).norm.natAbs.Coprime (m i) :=
    ((hmB i).of_dvd_right (hnormB i)).symm
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Nat.Coprime m) := by
    intro i _ j _ hij
    exact pairwise_coprime_m B (fun h => hij (he h))
  let r : ι → ℕ := fun i => (((t i : ℤ)*(f i).im - (f i).re) % (m i : ℤ)).toNat
  have hrint (i : ι) : (r i : ℤ) = ((t i : ℤ)*(f i).im - (f i).re) % m i :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hmpos i).ne'))
  have hr (i : ι) : (r i).Coprime (m i) := by
    apply (ZMod.isUnit_iff_coprime (r i) (m i)).mp
    have heq : (r i : ZMod (m i)) = (((t i : ℤ)*(f i).im - (f i).re : ℤ) : ZMod (m i)) := by
      have ht := congrArg (fun a : ℤ => (a : ZMod (m i))) (hrint i)
      simpa using ht
    rw [heq]
    exact unit_residue (t i) (f i) (hmnorm i)
  let a := Nat.chineseRemainderOfFinset r m Finset.univ (fun i _ => (hmpos i).ne') hcop
  let P : ℕ := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos fun i _ => hmpos i
  have hP4 : P.Coprime 4 := Nat.Coprime.prod_left fun i _ => hm4 i
  have haP : a.val.Coprime P := Nat.Coprime.prod_right fun i _ =>
    coprime_of_modEq (a.property i (Finset.mem_univ i)) (hr i)
  let A := Nat.chineseRemainder hP4 a.val 3
  have hAP : A.val.Coprime P := coprime_of_modEq A.property.1 haP
  have hA4 : A.val.Coprime 4 := coprime_of_modEq A.property.2 (by decide)
  have hAQ : A.val.Coprime (P*4) := hAP.mul_right hA4
  let T : ℕ := M + ∑ i, (m i + (f i).re.natAbs + 1)
  obtain ⟨p, hpT, hp, hpA⟩ := Nat.forall_exists_prime_gt_and_modEq T
    (by positivity : P*4 ≠ 0) hAQ
  have hp4 : p % 4 = 3 := by
    have he : p ≡ 3 [MOD 4] := (hpA.of_dvd (dvd_mul_left 4 P)).trans A.property.2
    exact he
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, by dsimp [T] at hpT; omega, hp,
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp4, ?_⟩
  intro i
  have hmiP : m i ∣ P := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hpmod : p ≡ r i [MOD m i] :=
    ((hpA.of_dvd (dvd_mul_of_dvd_left hmiP 4)).trans (A.property.1.of_dvd hmiP)).trans
      (a.property i (Finset.mem_univ i))
  have hpmod' : (p : ℤ) ≡ (t i : ℤ)*(f i).im - (f i).re [ZMOD m i] := by
    calc
      _ = (r i : ℤ) % m i := Int.natCast_modEq_iff.mpr hpmod
      _ = _ := by rw [hrint, Int.emod_emod]
  have hd : (m i : ℤ) ∣ (p : ℤ) + (f i).re - (t i : ℤ)*(f i).im := by
    convert dvd_neg.mpr (Int.modEq_iff_dvd.mp hpmod') using 1; ring
  have hsmall : m i + (f i).re.natAbs + 1 ≤ T := by
    have hs := Finset.single_le_sum (f := fun j => m j + (f j).re.natAbs + 1)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hs.trans (Nat.le_add_left _ _)
  have hreal : (m i : ℤ) < (p : ℤ) + (f i).re := by
    have ht : (m i : ℤ) + |(f i).re| + 1 < p := by
      have hh : m i + (f i).re.natAbs + 1 < p := hsmall.trans_lt hpT
      have hh' : (m i : ℤ) + ((f i).re.natAbs : ℤ) + 1 < p := by exact_mod_cast hh
      simpa using hh'
    have := neg_abs_le (f i).re
    omega
  let d : GaussianInt := ⟨t i, 1⟩
  have hdn : d.norm = (m i : ℤ) := by simp [d, gaussian_norm_sq, hm]
  apply not_prime_of_small_divisor (a := d)
  · apply gaussian_linear_divisor
    simpa [hm] using hd
  · rw [hdn]
    exact_mod_cast hmone i
  · rw [hdn, gaussian_norm_sq]
    simp only [Zsqrtd.re_add, Zsqrtd.re_natCast, Zsqrtd.im_add, Zsqrtd.im_natCast, zero_add]
    have hs := Int.le_self_sq ((p : ℤ) + (f i).re)
    nlinarith [sq_nonneg (f i).im]

/-- For every bound there are arbitrarily large Gaussian primes with no other
Gaussian prime at squared distance less than that bound. -/
theorem arbitrarily_large_isolated_primes (C : ℤ) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ Prime (p : GaussianInt) ∧
      ∀ z : GaussianInt, Prime z → (z - (p : GaussianInt)).norm < C → z = p := by
  classical
  let S : Set GaussianInt := {z | z ≠ 0 ∧ z.norm < C}
  have hS : S.Finite := (norm_sublevel_finite C).subset (fun _ h => h.2.le)
  letI : Fintype S := hS.fintype
  obtain ⟨p, hpM, hp, hpG, hiso⟩ := prime_with_prescribed_nonprime_offsets
    (fun z : S => z.val) (fun z => z.property.1) M
  refine ⟨p, hpM, hp, hpG, ?_⟩
  intro z hz hstep
  by_contra hne
  have hδ : z - (p : GaussianInt) ∈ S := ⟨sub_ne_zero.mpr hne, hstep⟩
  have hh := hiso ⟨z - (p : GaussianInt), hδ⟩
  have he : (p : GaussianInt) + (z - (p : GaussianInt)) = z := by abel
  exact hh (he.symm ▸ hz)

lemma no_neighbors_of_isolated {C : ℤ} {p : ℕ}
    (hiso : ∀ z : GaussianInt, Prime z → (z - (p : GaussianInt)).norm < C → z = p) :
    ∀ z : GaussianInt, ¬ (primeGraph C).Adj (p : GaussianInt) z := by
  intro z hz
  exact hz.2.2.1 (hiso z hz.2.1 hz.2.2.2).symm

lemma component_singleton_of_no_neighbors (C : ℤ) (z : GaussianInt)
    (h : ∀ w, ¬ (primeGraph C).Adj z w) :
    {w | (primeGraph C).Reachable z w} = {z} := by
  ext w
  constructor
  · rintro ⟨path⟩
    cases path with
    | nil => simp
    | cons hadj path => exact (h _ hadj).elim
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact SimpleGraph.Reachable.refl z

/-- There are infinitely many isolated prime vertices, for each fixed bound. -/
theorem infinitely_many_isolated_prime_vertices (C : ℤ) :
    Set.Infinite {z : GaussianInt | Prime z ∧ ∀ w, ¬ (primeGraph C).Adj z w} := by
  let S : Set ℕ := {p | Prime (p : GaussianInt) ∧ ∀ w, ¬ (primeGraph C).Adj (p : GaussianInt) w}
  have hS : S.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro M
    obtain ⟨p, hpM, _, hp, hiso⟩ := arbitrarily_large_isolated_primes C M
    exact ⟨p, ⟨hp, no_neighbors_of_isolated hiso⟩, hpM⟩
  have hinj : Function.Injective (fun p : ℕ => (p : GaussianInt)) := Nat.cast_injective
  apply (hS.image hinj.injOn).mono
  rintro z ⟨p, hp, rfl⟩
  exact hp

/-- The component can be certified as a singleton, but its center depends on
both the requested jump bound and the requested lower bound on location. -/
theorem arbitrarily_large_singleton_prime_components (C : ℤ) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ Prime (p : GaussianInt) ∧
      {w | (primeGraph C).Reachable (p : GaussianInt) w} = {(p : GaussianInt)} := by
  obtain ⟨p, hpM, _, hp, hiso⟩ := arbitrarily_large_isolated_primes C M
  exact ⟨p, hpM, hp, component_singleton_of_no_neighbors C (p : GaussianInt)
    (no_neighbors_of_isolated hiso)⟩

/-- Any hypothetical injective bounded-step prime walk must omit arbitrarily
large Gaussian primes. The original conjecture does not require surjectivity. -/
theorem prime_walk_omits_arbitrarily_large_primes (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ Prime (p : GaussianInt) ∧ ∀ n, x n ≠ (p : GaussianInt) := by
  obtain ⟨p, hpM, _, hp, hiso⟩ := arbitrarily_large_isolated_primes C M
  refine ⟨p, hpM, hp, ?_⟩
  intro n hn
  have hnext : x (n + 1) = (p : GaussianInt) :=
    hiso (x (n + 1)) (h (n + 1)).1 (by rw [← hn]; exact (h n).2)
  have he : n + 1 = n := hx (hnext.trans hn.symm)
  omega

#print axioms arbitrarily_large_isolated_primes
#print axioms infinitely_many_isolated_prime_vertices
#print axioms arbitrarily_large_singleton_prime_components
#print axioms prime_walk_omits_arbitrarily_large_primes

#print axioms prime_with_prescribed_nonprime_offsets

end IsolatedGaussianPrimes
end Erdos952Investigation
