import Submission.MinimumTernaryClass

/-!
# Private points of the ternary class in a global minimum odd cover

In a hypothetical globally minimum-cardinality odd cover, no strict odd
multiple of 3 contains all private points of the 3-class in one residue.
The theorem does not assert an odd covering witness or nonexistence.
-/
namespace Erdos7MinimumTernaryPrivate
open Erdos7Reduction Erdos7MinimumTernaryClass
open Erdos7PrivateReplacement Erdos7PrivateRefinementIsolation
open Erdos7ExchangePrivateTransfer (LabelMinimal)
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- Global cardinality minimality is independent of the chosen residues. -/
lemma global_label_minimal {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K) :
    LabelMinimal m := by
  classical
  change ∀ (b : I → ℤ) (j : I), ∃ x : ℤ, ∀ k, k ≠ j → ¬ (m k : ℤ) ∣ x-b k
  intro b j
  by_contra! hn
  have hc' : IsOddArithmeticCover m b :=
    ⟨hc.1,hc.2.1,fun x => by obtain ⟨k,_,hk⟩ := hn x; exact ⟨k,hk⟩⟩
  obtain ⟨x,hx⟩ := global_minimum_private m b hc' hmin j
  obtain ⟨k,hkj,hk⟩ := hn x
  exact hx.2 k hkj hk

/-- Replacing the ternary class by a missing nontrivial odd modulus cannot
retain all its private points, even without a divisibility assumption. -/
theorem private_escape_missing {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3) (d : ℕ) (hd : 1 < d ∧ Odd d)
    (hmissing : ∀ j, m j ≠ d) (b : ℤ) :
    ∃ x, Private m a i x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  by_contra! hn
  have h0 : OddCover 0 m a :=
    ⟨hc.1,fun k => ⟨(hc.2.1 k).1,(hc.2.1 k).2,dvd_zero _⟩,hc.2.2⟩
  have hnew := replace_private_cover 0 m a h0 i d b
    ⟨hd.1,hd.2,dvd_zero _⟩ hmissing hn
  have hc' : IsOddArithmeticCover (Function.update m i d) (Function.update a i b) :=
    ⟨hnew.1,fun k => ⟨(hnew.2.1 k).1,(hnew.2.1 k).2.1⟩,hnew.2.2⟩
  obtain ⟨j,hj⟩ := minimum_contains_three _ _ hc' hmin
  by_cases hji : j=i
  · subst j
    have hd3 : d=3 := by simpa using hj
    exact hmissing i (hi.trans hd3.symm)
  · have hmj : m j=3 := by simpa [hji] using hj
    exact hji (hc.1 (hmj.trans hi.symm))

/-- Every strict odd multiple of 3 has a private escape from every residue,
including when the finer modulus is already used by another class. -/
theorem private_escape_multiple {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3) (d : ℕ) (hd : 3 < d ∧ Odd d) (hd3 : 3 ∣ d)
    (b : ℤ) :
    ∃ x, Private m a i x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  by_cases hex : ∃ j, m j=d
  · obtain ⟨j,hj⟩ := hex
    by_contra! hn
    have hji : j ≠ i := by intro h; subst j; omega
    have hdiv : m i ∣ m j := by simpa only [hi,hj] using hd3
    have hlabel := global_label_minimal m a hc hmin
    have hiso := refinement_forces_isolation m a hlabel hc.2.2 i j hji hdiv b
      (by simpa only [hj] using hn)
    have hsep : ¬ (3 : ℤ) ∣ a i-a j := by
      intro ha
      obtain ⟨x,hx⟩ := global_minimum_private m a hc hmin j
      have h3x : (3 : ℤ) ∣ x-a j :=
        (Int.natCast_dvd_natCast.mpr (by simpa only [hj] using hd3)).trans hx.1
      apply hx.2 i (Ne.symm hji)
      rw [hi]
      convert dvd_sub h3x ha using 1 <;> ring
    have hall : ∀ k, k ≠ j → 3 ∣ m k → ¬ (3 : ℤ) ∣ a k-a j := by
      intro k hkj hk3
      by_cases hki : k=i
      · simpa only [hki] using hsep
      · simpa only [hi] using hiso k hki hkj (by simpa only [hi] using hk3)
    have hjthree := isolated_ternary_modulus m a hc hmin j
      (by simpa only [hj] using hd3) hall
    omega
  · apply private_escape_missing m a hc hmin i hi d ⟨by omega,hd.2⟩ _ b
    simpa using hex

/-- Private points are periodic with every common period of the moduli. -/
lemma private_add_period {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (P : ℕ) (hP : ∀ k, m k ∣ P) (i : I) (x : ℤ) (hx : Private m a i x) :
    Private m a i (x+P) := by
  have hp (k : I) : (m k : ℤ) ∣ (P : ℤ) := Int.natCast_dvd_natCast.mpr (hP k)
  refine ⟨?_,?_⟩
  · convert dvd_add hx.1 (hp i) using 1 <;> ring
  · intro k hki hk
    apply hx.2 k hki
    convert dvd_sub hk (hp k) using 1 <;> ring

/-- An integer modulus containing all differences of private points of the
ternary class must divide 3. This includes even and zero candidate moduli. -/
theorem private_difference_divisor {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3) (d : ℕ)
    (hspan : ∀ x y : ℤ, Private m a i x → Private m a i y → (d : ℤ) ∣ x-y) :
    d ∣ 3 := by
  classical
  obtain ⟨x₀,hx₀⟩ := global_minimum_private m a hc hmin i
  let P := ∏ k, m k
  have hP : ∀ k, m k ∣ P := fun k => Finset.dvd_prod_of_mem m (Finset.mem_univ k)
  have hPodd : Odd P := Finset.prod_induction m Odd
    (fun _ _ hu hv => hu.mul hv) (by norm_num) (fun k _ => (hc.2.1 k).2)
  have hdP : d ∣ P := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [add_sub_cancel_left] using
      hspan (x₀+P) x₀ (private_add_period m a P hP i x₀ hx₀) hx₀
  have hdo : Odd d := hPodd.of_dvd_nat hdP
  by_contra hnd
  have hdgt : 1 < d := by
    have hd0 : d ≠ 0 := by intro h; rw [h] at hdo; norm_num at hdo
    have hd1 : d ≠ 1 := by intro h; exact hnd (h ▸ one_dvd 3)
    omega
  have h3span : ∀ x : ℤ, Private m a i x → (3 : ℤ) ∣ x-x₀ := by
    intro x hx
    have hx3 : (3 : ℤ) ∣ x-a i := by simpa only [hi] using hx.1
    have h03 : (3 : ℤ) ∣ x₀-a i := by simpa only [hi] using hx₀.1
    convert dvd_sub hx3 h03 using 1 <;> ring
  by_cases hd3 : 3 ∣ d
  · have hbig : 3 < d := by
      have hle := Nat.le_of_dvd (by omega : 0 < d) hd3
      have hne : d ≠ 3 := by intro h; apply hnd; rw [h]
      omega
    obtain ⟨x,hx,hn⟩ := private_escape_multiple m a hc hmin i hi d ⟨hbig,hdo⟩ hd3 x₀
    exact hn (hspan x x₀ hx hx₀)
  · have hcp : IsCoprime (3 : ℤ) (d : ℤ) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hd3).isCoprime
    have hodd : Odd (3*d) := (show Odd (3 : ℕ) by decide).mul hdo
    obtain ⟨x,hx,hn⟩ := private_escape_multiple m a hc hmin i hi (3*d)
      ⟨by omega,hodd⟩ (dvd_mul_right 3 d) x₀
    apply hn
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      hcp.mul_dvd (h3span x hx) (hspan x x₀ hx hx₀)

/-- The affine arithmetic span of the ternary class's private points is exactly
its original residue class, not a proper arithmetic subprogression. -/
theorem private_residue_iff {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hmin : ∀ N K, HasOddArithmeticCover N K → Fintype.card I ≤ K)
    (i : I) (hi : m i = 3) (d : ℕ) (b : ℤ) :
    (∀ x, Private m a i x → (d : ℤ) ∣ x-b) ↔
      d ∣ 3 ∧ (d : ℤ) ∣ a i-b := by
  constructor
  · intro hh
    have hd := private_difference_divisor m a hc hmin i hi d (by
      intro x y hx hy
      convert dvd_sub (hh x hx) (hh y hy) using 1 <;> ring)
    refine ⟨hd,?_⟩
    obtain ⟨x,hx⟩ := global_minimum_private m a hc hmin i
    have hdx : (d : ℤ) ∣ x-a i :=
      (Int.natCast_dvd_natCast.mpr (by simpa only [hi] using hd)).trans hx.1
    convert dvd_sub (hh x hx) hdx using 1 <;> ring
  · rintro ⟨hd,ha⟩ x hx
    have hdx : (d : ℤ) ∣ x-a i :=
      (Int.natCast_dvd_natCast.mpr (by simpa only [hi] using hd)).trans hx.1
    simpa only [sub_add_sub_cancel] using dvd_add hdx ha

#print axioms global_label_minimal
#print axioms private_escape_missing
#print axioms private_escape_multiple
#print axioms private_difference_divisor
#print axioms private_residue_iff
end Erdos7MinimumTernaryPrivate
