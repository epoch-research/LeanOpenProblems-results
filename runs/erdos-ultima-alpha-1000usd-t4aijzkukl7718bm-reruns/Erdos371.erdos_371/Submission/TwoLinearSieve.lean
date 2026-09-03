import FormalConjecturesUtil
import Submission.ResidueSieve

/-! A coefficient-uniform finite sieve for two linear forms of determinant
one. Quantitative bounds on the Euler product and coefficient sums are separate. -/

namespace Erdos371TwoLinearSieve

open Finset Erdos371FiniteBrun Erdos371ResidueSieve

attribute [local instance] Classical.propDecidable

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def fieldRoots (a b c d : F) : Finset F :=
  Finset.univ.filter fun x => (a*x+b)*(c*x+d)=0

lemma linear_zero_iff {a : F} (ha : a ≠ 0) (b x : F) : a*x+b=0 ↔ x = -b/a := by
  rw [eq_div_iff ha]
  constructor <;> intro h <;> linear_combination h

lemma fieldRoots_card {a b c d : F} (hdet : a*d-b*c ≠ 0) :
    (fieldRoots a b c d).card = if a*c=0 then 1 else 2 := by
  by_cases ha : a=0
  · have hb : b ≠ 0 := by intro hb; simp [ha,hb] at hdet
    have hc : c ≠ 0 := by intro hc; simp [ha,hc] at hdet
    have he : fieldRoots a b c d = {-d/c} := by
      ext x
      simp [fieldRoots, ha, hb, linear_zero_iff hc]
    rw [he]
    simp [ha]
  · by_cases hc : c=0
    · have hd : d ≠ 0 := by intro hd; simp [hc,hd] at hdet
      have he : fieldRoots a b c d = {-b/a} := by
        ext x
        simp [fieldRoots, hc, hd, linear_zero_iff ha]
      rw [he]
      simp [hc]
    · have he : fieldRoots a b c d = {-b/a, -d/c} := by
        ext x
        simp [fieldRoots, mul_eq_zero, linear_zero_iff ha, linear_zero_iff hc]
      have hne : -b/a ≠ -d/c := by
        intro h
        have h1 := (linear_zero_iff ha b (-b/a)).mpr rfl
        have h2 := (linear_zero_iff hc d (-d/c)).mpr rfl
        rw [h] at h1
        apply hdet
        linear_combination a*h2-c*h1
      simp [he, mul_ne_zero ha hc, Finset.card_pair hne]
end Field

noncomputable def linearResidues (a b c d p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun n => p ∣ (a*n+b)*(c*n+d)

lemma linearResidues_subset (a b c d p : ℕ) :
    linearResidues a b c d p ⊆ Finset.range p := Finset.filter_subset _ _

lemma linearResidues_card_field {p : ℕ} [Fact p.Prime] (a b c d : ℕ) :
    (linearResidues a b c d p).card =
      (fieldRoots (a:ZMod p) b c d).card := by
  apply Finset.card_bij (fun n (_ : n ∈ linearResidues a b c d p) => (n:ZMod p))
  · intro n hn
    obtain ⟨_, hd⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hh := (ZMod.natCast_eq_zero_iff ((a*n+b)*(c*n+d)) p).mpr hd
    push_cast at hh
    exact hh
  · intro n hn m hm he
    have hn0 := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hm0 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    have hh := congrArg ZMod.val he
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hm0] using hh
  · intro x hx
    have hz := (Finset.mem_filter.mp hx).2
    have hn : x.val ∈ linearResidues a b c d p := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
      apply (ZMod.natCast_eq_zero_iff _ p).mp
      push_cast
      simpa only [ZMod.natCast_zmod_val] using hz
    exact ⟨x.val, hn, ZMod.natCast_zmod_val x⟩

def determinantOne (a b c d : ℕ) : Prop := a*d = b*c+1 ∨ b*c = a*d+1

lemma linearResidues_card {p a b c d : ℕ} (hp : p.Prime) (hdet : determinantOne a b c d) :
    (linearResidues a b c d p).card = if p ∣ a*c then 1 else 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [linearResidues_card_field]
  have hd : (a:ZMod p)*d - b*c ≠ 0 := by
    intro hz
    rcases hdet with h | h
    · have hh : (a:ZMod p)*d = (b:ZMod p)*c+1 := by
        have hh := congrArg (fun n : ℕ => (n:ZMod p)) h
        push_cast at hh
        exact hh
      have he : (1:ZMod p)=0 := by linear_combination hz-hh
      exact one_ne_zero he
    · have hh : (b:ZMod p)*c = (a:ZMod p)*d+1 := by
        have hh := congrArg (fun n : ℕ => (n:ZMod p)) h
        push_cast at hh
        exact hh
      have he : (1:ZMod p)=0 := by linear_combination -hz-hh
      exact one_ne_zero he
  rw [fieldRoots_card hd]
  have he : (a:ZMod p)*c=0 ↔ p ∣ a*c := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  simp only [he]

noncomputable def linearDensity (a c p : ℕ) : ℝ := (if p ∣ a*c then 1 else 2)/(p:ℝ)

lemma localDensity_linearResidues {p a b c d : ℕ} (hp : p.Prime)
    (hdet : determinantOne a b c d) :
    localDensity (linearResidues a b c d) p = linearDensity a c p := by
  unfold localDensity linearDensity
  rw [linearResidues_card hp hdet]
  split_ifs <;> norm_num

/-- A finite upper bound uniform in the four coefficients. The sieve level
and prime cutoff remain parameters; no asymptotic cancellation is inferred. -/
theorem two_linear_sifted_upper {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {a b c d : ℕ} (hdet : determinantOne a b c d) (N : ℕ)
    {r : ℕ} (hr : 0 < r) (hlarge : 4*(∑ p ∈ s, linearDensity a c p)^2 ≤ (r:ℝ)) :
    (survivors (Finset.range N) s (residueEvent (linearResidues a b c d))).card ≤
      (N:ℝ)*((∏ p ∈ s, (1-linearDensity a c p)) + (1/4:ℝ)^r) +
        (2*r+1:ℕ) * (2*(max 1 s.card):ℝ)^(2*r) := by
  have hd (p : ℕ) (hp : p ∈ s) := localDensity_linearResidues (hs p hp) hdet
  have hsum : (∑ p ∈ s, localDensity (linearResidues a b c d) p) =
      ∑ p ∈ s, linearDensity a c p := Finset.sum_congr rfl hd
  have hprod : (∏ p ∈ s, (1-localDensity (linearResidues a b c d) p)) =
      ∏ p ∈ s, (1-linearDensity a c p) := Finset.prod_congr rfl (fun p hp => by rw [hd p hp])
  have hh := residue_sieve_upper hs (linearResidues a b c d)
    (fun p _ => linearResidues_subset a b c d p)
    (fun p hp => by rw [linearResidues_card (hs p hp) hdet]; split_ifs <;> omega)
    N hr (by simpa only [hsum] using hlarge)
  simpa only [hprod] using hh


lemma residueEvent_linear_iff {p : ℕ} (hp : 0 < p) (a b c d n : ℕ) :
    residueEvent (linearResidues a b c d) p n ↔ p ∣ (a*n+b)*(c*n+d) := by
  simp only [residueEvent, linearResidues, Finset.mem_filter, Finset.mem_range,
    Nat.mod_lt n hp, true_and]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.mul_mod, Nat.add_mod]

noncomputable def primeInputs (s : Finset ℕ) (a b c d N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => (a*n+b).Prime ∧ (c*n+d).Prime ∧
    ∀ p ∈ s, p < a*n+b ∧ p < c*n+d

lemma primeInputs_subset_survivors {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (a b c d N : ℕ) :
    primeInputs s a b c d N ⊆
      survivors (Finset.range N) s (residueEvent (linearResidues a b c d)) := by
  intro n hn
  obtain ⟨hnN, h1, h2, hlarge⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hnN, ?_⟩
  intro p hp hbad
  have hdiv := (residueEvent_linear_iff (hs p hp).pos a b c d n).mp hbad
  rcases (hs p hp).dvd_mul.mp hdiv with h | h
  · rcases (Nat.dvd_prime h1).mp h with h | h
    · exact (hs p hp).ne_one h
    · exact (ne_of_lt (hlarge p hp).1) h
  · rcases (Nat.dvd_prime h2).mp h with h | h
    · exact (hs p hp).ne_one h
    · exact (ne_of_lt (hlarge p hp).2) h

/-- The sieve bound applies to prime values of both forms once they exceed
all of the sieving primes. -/
theorem two_linear_prime_upper {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {a b c d : ℕ} (hdet : determinantOne a b c d) (N : ℕ)
    {r : ℕ} (hr : 0 < r) (hlarge : 4*(∑ p ∈ s, linearDensity a c p)^2 ≤ (r:ℝ)) :
    (primeInputs s a b c d N).card ≤
      (N:ℝ)*((∏ p ∈ s, (1-linearDensity a c p)) + (1/4:ℝ)^r) +
        (2*r+1:ℕ) * (2*(max 1 s.card):ℝ)^(2*r) := by
  exact (Nat.cast_le.mpr (Finset.card_le_card (primeInputs_subset_survivors hs a b c d N))).trans
    (two_linear_sifted_upper hs hdet N hr hlarge)


end Erdos371TwoLinearSieve

#print axioms Erdos371TwoLinearSieve.linearResidues_card
#print axioms Erdos371TwoLinearSieve.two_linear_sifted_upper
#print axioms Erdos371TwoLinearSieve.two_linear_prime_upper
