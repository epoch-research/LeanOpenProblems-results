import Submission.ThreeResidueProgressionSieve

/-! Distinct local sieve roots for a prime and two signed neighboring
linear forms. The shifts are integers so both orientations are covered. -/
namespace Erdos371.FiniteSieve
open Finset

noncomputable def integerLinearResidues (p a : ℕ) (b : ℤ) : Finset ℕ :=
  (range p).filter fun n => (p : ℤ) ∣ (a : ℤ)*n+b

lemma integerLinearResidues_card (p a : ℕ) (b : ℤ) (hp : p.Prime) (ha : ¬p ∣ a) :
    (integerLinearResidues p a b).card=1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let x : ZMod p := -(b : ZMod p)/(a : ZMod p)
  have haZ : (a : ZMod p) ≠ 0 := by
    intro he
    exact ha ((ZMod.natCast_eq_zero_iff a p).mp he)
  have hxZ : (a : ZMod p)*x+b=0 := by
    dsimp only [x]
    field_simp
    ring
  have hx : (p : ℤ) ∣ (a : ℤ)*x.val+b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hxZ
  apply card_eq_one.mpr
  refine ⟨x.val,?_⟩
  ext n
  simp only [integerLinearResidues,mem_filter,mem_range,mem_singleton]
  constructor
  · rintro ⟨hn,hd⟩
    have hnZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    push_cast at hnZ
    have he : (n : ZMod p)=x := by
      apply mul_left_cancel₀ haZ
      linear_combination hnZ-hxZ
    have he' : (n : ZMod p)=(x.val : ZMod p) := by rwa [ZMod.natCast_zmod_val]
    exact ((ZMod.natCast_eq_natCast_iff n x.val p).mp he').eq_of_lt_of_lt hn (ZMod.val_lt x)
  · rintro rfl
    exact ⟨ZMod.val_lt x,hx⟩

lemma integerLinearResidues_disjoint (p a c : ℕ) (b d : ℤ)
    (hdet0 : (c : ℤ)*b-a*d ≠ 0) (hdet : ((c : ℤ)*b-a*d).natAbs < p) :
    Disjoint (integerLinearResidues p a b) (integerLinearResidues p c d) := by
  classical
  apply disjoint_left.mpr
  intro n hn hn'
  have h₁ := (mem_filter.mp hn).2
  have h₂ := (mem_filter.mp hn').2
  have hd : (p : ℤ) ∣ (c : ℤ)*b-a*d := by
    convert dvd_sub (dvd_mul_of_dvd_right h₁ (c : ℤ))
      (dvd_mul_of_dvd_right h₂ (a : ℤ)) using 1; ring
  have hh := Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd.mp hd) hdet
  exact hdet0 (Int.natAbs_eq_zero.mp hh)

noncomputable def threePrimeResidues (p k l : ℕ) (ε δ : ℤ) : Finset ℕ :=
  {0} ∪ integerLinearResidues p k ε ∪ integerLinearResidues p l δ

lemma threePrimeResidues_subset (p k l : ℕ) (ε δ : ℤ) (hp : 0 < p) :
    threePrimeResidues p k l ε δ ⊆ range p :=
  union_subset (union_subset (singleton_subset_iff.mpr (mem_range.mpr hp))
    (filter_subset _ _)) (filter_subset _ _)

lemma threePrimeResidues_card (p k l : ℕ) (ε δ : ℤ) (hp : p.Prime)
    (hk : ¬p ∣ k) (hl : ¬p ∣ l) (hε : ε.natAbs=1) (hδ : δ.natAbs=1)
    (hdet0 : (l : ℤ)*ε-k*δ ≠ 0) (hdet : ((l : ℤ)*ε-k*δ).natAbs < p) :
    (threePrimeResidues p k l ε δ).card=3 := by
  classical
  have hzero (a : ℕ) (e : ℤ) (he : e.natAbs=1) :
      Disjoint ({0} : Finset ℕ) (integerLinearResidues p a e) := by
    rw [disjoint_singleton_left]
    intro hh
    have hd : (p : ℤ) ∣ e := by simpa using (mem_filter.mp hh).2
    have hd' : p ∣ 1 := by simpa only [he] using Int.natCast_dvd.mp hd
    exact hp.not_dvd_one hd'
  rw [threePrimeResidues,card_union_of_disjoint (disjoint_union_left.mpr
    ⟨hzero l δ hδ,integerLinearResidues_disjoint p k l ε δ hdet0 hdet⟩),
    card_union_of_disjoint (hzero k ε hε),card_singleton,
    integerLinearResidues_card p k ε hp hk,integerLinearResidues_card p l δ hp hl]

lemma mod_mem_integerLinearResidues (p k n : ℕ) (e : ℤ) (hp : 0 < p) :
    n%p ∈ integerLinearResidues p k e ↔ (p : ℤ) ∣ (k : ℤ)*n+e := by
  have hh : (p : ℤ) ∣ (k : ℤ)*((n%p : ℕ) : ℤ)+e ↔ (p : ℤ) ∣ (k : ℤ)*n+e := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rfl
  simp only [integerLinearResidues,mem_filter,mem_range,Nat.mod_lt n hp,true_and,hh]

lemma mod_mem_threePrimeResidues (p k l n : ℕ) (ε δ : ℤ) (hp : 0 < p) :
    n%p ∈ threePrimeResidues p k l ε δ ↔
      p ∣ n ∨ (p : ℤ) ∣ (k : ℤ)*n+ε ∨ (p : ℤ) ∣ (l : ℤ)*n+δ := by
  simp only [threePrimeResidues,mem_union,mem_singleton,
    mod_mem_integerLinearResidues p k n ε hp,mod_mem_integerLinearResidues p l n δ hp,
    ← Nat.dvd_iff_mod_eq_zero,or_assoc]

#print axioms threePrimeResidues_card
#print axioms mod_mem_threePrimeResidues
end Erdos371.FiniteSieve
