import Submission.SievePeriodicDrift
import Submission.RecurrentIncrementObstruction

/-! Long repeated increment blocks in an admissible walk have highly divisible
return displacements. This does not assume periodicity or recurrence. -/
namespace Erdos952Investigation
namespace ReturnDisplacementObstruction

open RecurrentIncrementObstruction SievePeriodicDrift

set_option maxHeartbeats 0

lemma finite_group_prefix_translation {G : Type*} [AddCommGroup G] [Finite G]
    (f : ℕ → G) :
    ∃ L : ℕ, ∀ n : ℕ, ∀ d : G,
      (∀ i ≤ L, f (n + i) = f i + d) →
      ∀ m : ℕ, f 0 + m • d ∈ Set.range f := by
  classical
  let S := Set.range f
  letI : Fintype S := Fintype.ofFinite S
  let rep : S → ℕ := fun s => Classical.choose s.property
  have hrep (s : S) : f (rep s) = s.val := Classical.choose_spec s.property
  let L : ℕ := Finset.univ.sup rep
  have hle (s : S) : rep s ≤ L := Finset.le_sup (Finset.mem_univ s)
  refine ⟨L, ?_⟩
  intro n d hform m
  have hclosed (s : G) (hs : s ∈ S) : s + d ∈ S := by
    exact ⟨n + rep ⟨s, hs⟩, (hform _ (hle ⟨s, hs⟩)).trans (by rw [hrep])⟩
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    simpa only [succ_nsmul, add_assoc] using hclosed _ ih

/-- The residue range of a walk avoiding the split norm-zero locus has no
nontrivial translation stabilizer. Consequently a long enough repeated
increment prefix has zero displacement modulo the split prime. -/
theorem split_prime_divides_long_return (x : ℕ → GaussianInt) (p : ℕ)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (ha : ∃ a b : ZMod p, ∀ n, AdmissibleRay.Good p a b (x n)) :
    ∃ L : ℕ, ∀ n : ℕ,
      (∀ i < L, x (n + i + 1) - x (n + i) = x (i + 1) - x i) →
      (p : ℤ) ∣ (x n - x 0).re ∧ (p : ℤ) ∣ (x n - x 0).im := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := ha
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hr2 : r^2 = -1 := by simpa [pow_two] using hr.symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
    have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  obtain ⟨L, htrans⟩ := finite_group_prefix_translation (fun n => residue p (x n))
  refine ⟨L, ?_⟩
  intro n hword
  let d := residue p (x n) - residue p (x 0)
  have hform (i : ℕ) (hi : i ≤ L) :
      residue p (x (n + i)) = residue p (x i) + d := by
    rw [block_position_formula x n L hword i hi, map_add, map_sub]
    dsimp [d]
    abel
  have hline (t : ZMod p) :
      (a + (x 0).re + t * ((x n - x 0).re : ZMod p))^2 +
        (b + (x 0).im + t * ((x n - x 0).im : ZMod p))^2 ≠ 0 := by
    obtain ⟨j, hj⟩ := htrans n d hform t.val
    have hre := congrArg Prod.fst hj
    have him := congrArg Prod.snd hj
    change ((x j).re : ZMod p) = (x 0).re + t.val •
      (((x n).re : ZMod p) - (x 0).re) at hre
    change ((x j).im : ZMod p) = (x 0).im + t.val •
      (((x n).im : ZMod p) - (x 0).im) at him
    simp only [nsmul_eq_mul, ZMod.natCast_zmod_val] at hre him
    have hh := hab j
    simp only [AdmissibleRay.Good, hre, him] at hh
    simpa only [Zsqrtd.re_sub, Zsqrtd.im_sub, Int.cast_sub, add_assoc] using hh
  obtain ⟨hre, him⟩ := slope_zero_of_norm_ne_zero r
    (a + (x 0).re) (b + (x 0).im)
    ((x n - x 0).re : ZMod p) ((x n - x 0).im : ZMod p) hr2 h2 hline
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hre,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp him⟩

/-- A single finite prefix controls the displacement at all split primes up to
any prescribed cutoff. The length of that prefix is not bounded here. -/
theorem splitPrimorial_divides_long_return (x : ℕ → GaussianInt) (S : ℕ)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p,
      ∀ n, AdmissibleRay.Good p a b (x n)) :
    ∃ L : ℕ, ∀ n : ℕ,
      (∀ i < L, x (n + i + 1) - x (n + i) = x (i + 1) - x i) →
      (splitPrimorial S : ℤ) ∣ (x n - x 0).re ∧
        (splitPrimorial S : ℤ) ∣ (x n - x 0).im := by
  classical
  let T := (Finset.range (S + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)
  have hmem {p : ℕ} (hp : p ∈ T) : p ≤ S ∧ p.Prime ∧ p % 4 = 1 := by
    simpa only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] using hp
  have hlocal (p : T) : ∃ L : ℕ, ∀ n : ℕ,
      (∀ i < L, x (n + i + 1) - x (n + i) = x (i + 1) - x i) →
      (p.val : ℤ) ∣ (x n - x 0).re ∧ (p.val : ℤ) ∣ (x n - x 0).im :=
    split_prime_divides_long_return x p.val (hmem p.property).2.1
      (hmem p.property).2.2 (ha p.val (hmem p.property).1 (hmem p.property).2.1)
  choose len hlen using hlocal
  let L := Finset.univ.sup len
  refine ⟨L, ?_⟩
  intro n hword
  have hcop : (T : Set ℕ).Pairwise (Function.onFun IsCoprime (fun p : ℕ => (p : ℤ))) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (hmem hp).2.1 (hmem hq).2.1).mpr hpq).isCoprime
  have hcoords (p : ℕ) (hp : p ∈ T) :
      (p : ℤ) ∣ (x n - x 0).re ∧ (p : ℤ) ∣ (x n - x 0).im := by
    apply hlen ⟨p, hp⟩ n
    intro i hi
    exact hword i (hi.trans_le (show len ⟨p, hp⟩ ≤ L from Finset.le_sup (Finset.mem_univ (⟨p, hp⟩ : T))))
  have hr := Finset.prod_dvd_of_coprime hcop (fun p hp => (hcoords p hp).1)
  have hi := Finset.prod_dvd_of_coprime hcop (fun p hp => (hcoords p hp).2)
  simpa only [splitPrimorial, Nat.cast_prod, T] using And.intro hr hi

/-- Every nontrivial return to a sufficiently long prefix costs at least the
split primorial in taxicab displacement, and hence in time times step bound. -/
theorem long_return_lower_bound (x : ℕ → GaussianInt) (C : ℤ) (S : ℕ)
    (hx : Function.Injective x)
    (hs : ∀ n, (x (n + 1) - x n).norm < C)
    (ha : ∀ p ≤ S, p.Prime → ∃ a b : ZMod p,
      ∀ n, AdmissibleRay.Good p a b (x n)) :
    ∃ L : ℕ, ∀ n : ℕ, 0 < n →
      (∀ i < L, x (n + i + 1) - x (n + i) = x (i + 1) - x i) →
      (splitPrimorial S : ℤ) ≤ (n : ℤ) * C := by
  obtain ⟨L, hL⟩ := splitPrimorial_divides_long_return x S ha
  refine ⟨L, ?_⟩
  intro n hn hword
  obtain ⟨hr, hi⟩ := hL n hword
  have hd : x n - x 0 ≠ 0 := by
    intro he
    exact (Nat.ne_of_gt hn) (hx (sub_eq_zero.mp he))
  have hbound := (le_taxicab_of_dvd_coordinates hd hr hi).trans
    (by simpa using taxicab_drift_le x C hs 0 n)
  exact hbound

#print axioms split_prime_divides_long_return
#print axioms splitPrimorial_divides_long_return
#print axioms long_return_lower_bound

end ReturnDisplacementObstruction
end Erdos952Investigation
