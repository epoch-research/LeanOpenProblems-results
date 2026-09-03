import Submission.PrivateReplacement

/-!
# Private periods of pure prime-power classes

These are structural lemmas for irredundant partial families. They do not
settle the odd strict covering conjecture and require no oddness or coverage.
-/
namespace Erdos7PurePowerPrivatePeriod
open Erdos7PrivateReplacement
set_option maxHeartbeats 1000000

lemma disjoint_of_dvd {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hp : ∀ j, ∃ y, Private m a j y) {i j : I} (hji : j ≠ i)
    (hd : m i ∣ m j) (x : ℤ) (hi : (m i : ℤ) ∣ x-a i) :
    ¬ (m j : ℤ) ∣ x-a j := by
  intro hj
  obtain ⟨y, hy⟩ := hp j
  have hd' : (m i : ℤ) ∣ (m j : ℤ) := by exact_mod_cast hd
  apply hy.2 i hji.symm
  have hh := ((hd'.trans hy.1).sub (hd'.trans hj)).add hi
  convert hh using 1 <;> ring

/-- A period for the lower/incomparable labels is also a period of the entire
private set: proper superclasses are disjoint and need not be preserved. -/
theorem private_add_step {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hp : ∀ j, ∃ y, Private m a j y) (i : I) (L : ℕ)
    (hiL : m i ∣ L) (hL : ∀ j, ¬ m i ∣ m j → m j ∣ L)
    {x : ℤ} (hx : Private m a i x) (t : ℤ) :
    Private m a i (x+(L : ℤ)*t) := by
  have hiL' : (m i : ℤ) ∣ (L : ℤ) := by exact_mod_cast hiL
  have hh : (m i : ℤ) ∣ x+(L : ℤ)*t-a i := by
    convert hx.1.add (hiL'.mul_right t) using 1 <;> ring
  refine ⟨hh, ?_⟩
  intro j hji hj
  by_cases hd : m i ∣ m j
  · exact disjoint_of_dvd m a hp hji hd _ hh hj
  · have hjL : (m j : ℤ) ∣ (L : ℤ) := by exact_mod_cast hL j hd
    apply hx.2 j hji
    convert hj.sub (hjL.mul_right t) using 1 <;> ring

lemma finite_lcm_factorization_le {I : Type*} (s : Finset I) (m : I → ℕ)
    (p e : ℕ) (hm : ∀ j ∈ s, m j ≠ 0)
    (he : ∀ j ∈ s, (m j).factorization p ≤ e) :
    (s.lcm m).factorization p ≤ e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
    have hj0 := hm j (Finset.mem_insert_self _ _)
    have hs0 : s.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr
      (fun k hk => hm k (Finset.mem_insert_of_mem hk))
    rw [Finset.lcm_insert, lcm_eq_nat_lcm, Nat.factorization_lcm hj0 hs0,
      Finsupp.sup_apply]
    exact max_le (he j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hm k (Finset.mem_insert_of_mem hk))
        (fun k hk => he k (Finset.mem_insert_of_mem hk)))

/-- The private period can be chosen to have exactly the old p-adic exponent. -/
theorem exists_pure_step {I : Type*} [Fintype I] (m : I → ℕ)
    (hm : ∀ j, m j ≠ 0) (i : I) {p e : ℕ} (hp : p.Prime)
    (hi : m i=p^e) :
    ∃ L : ℕ, L ≠ 0 ∧ m i ∣ L ∧
      (∀ j, ¬ m i ∣ m j → m j ∣ L) ∧ L.factorization p=e := by
  classical
  let s := Finset.univ.filter (fun j => ¬ m i ∣ m j)
  let K := s.lcm m
  have hK0 : K ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun j _ => hm j)
  have heK : K.factorization p ≤ e := by
    apply finite_lcm_factorization_le s m p e (fun j _ => hm j)
    intro j hj
    have hn := (Finset.mem_filter.mp hj).2
    rw [hi, hp.pow_dvd_iff_le_factorization (hm j)] at hn
    omega
  refine ⟨Nat.lcm (p^e) K, Nat.lcm_ne_zero (pow_ne_zero _ hp.ne_zero) hK0,
    ?_, ?_, ?_⟩
  · rw [hi]; exact Nat.dvd_lcm_left _ _
  · intro j hj
    exact (Finset.dvd_lcm (show j ∈ s from Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hj⟩)).trans (Nat.dvd_lcm_right _ _)
  · rw [Nat.factorization_lcm (pow_ne_zero _ hp.ne_zero) hK0,
      Finsupp.sup_apply, Nat.factorization_pow_self hp]
    exact max_eq_left heK

/-- No single strictly finer p-adic class can contain all private points of a
pure p-power label. This holds for every irredundant partial family. -/
theorem private_escape_finer {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℤ)
    (hm : ∀ j, m j ≠ 0) (hpriv : ∀ j, ∃ y, Private m a j y)
    (i : I) {p e f : ℕ} (hp : p.Prime) (hi : m i=p^e) (hef : e<f)
    (b : ℤ) : ∃ x, Private m a i x ∧ ¬ ((p^f : ℕ) : ℤ) ∣ x-b := by
  obtain ⟨L,hL0,hiL,hL,heL⟩ := exists_pure_step m hm i hp hi
  obtain ⟨x,hx⟩ := hpriv i
  by_cases hb : ((p^f : ℕ) : ℤ) ∣ x-b
  · refine ⟨x+(L : ℤ)*1, private_add_step m a hpriv i L hiL hL hx 1, ?_⟩
    intro hz
    have hd : ((p^f : ℕ) : ℤ) ∣ (L : ℤ) := by
      convert hz.sub hb using 1 <;> ring
    have hd' : p^f ∣ L := by exact_mod_cast hd
    have hle := (hp.pow_dvd_iff_le_factorization hL0).mp hd'
    rw [heL] at hle
    omega
  · exact ⟨x,hx,hb⟩

/-- Coprime multiplication reaches every residue, expressed as divisibility. -/
lemma affine_parameter {c q : ℕ} (h : c.Coprime q) (k : ℤ) :
    ∃ t : ℤ, (q : ℤ) ∣ (c : ℤ)*t-k := by
  obtain ⟨u,v,hu⟩ := h.isCoprime
  refine ⟨u*k,-v*k,?_⟩
  linear_combination k*hu

/-- At every finer p-adic level, the private set meets EVERY child of its old
class, not just two children. The old class need not belong to a cover. -/
theorem every_finer_residue {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℤ)
    (hm : ∀ j, m j ≠ 0) (hpriv : ∀ j, ∃ y, Private m a j y)
    (i : I) {p e f : ℕ} (hp : p.Prime) (hi : m i=p^e) (hef : e≤f)
    (b : ℤ) (hb : (m i : ℤ) ∣ b-a i) :
    ∃ y, Private m a i y ∧ ((p^f : ℕ) : ℤ) ∣ y-b := by
  obtain ⟨L,hL0,hiL,hL,heL⟩ := exists_pure_step m hm i hp hi
  obtain ⟨c,hc⟩ := (show p^e ∣ L by simpa [hi] using hiL)
  have hpc : ¬ p ∣ c := by
    intro h
    have hd : p^(e+1) ∣ L := by
      obtain ⟨z,hz⟩ := h
      refine ⟨z,?_⟩
      rw [hc,hz,pow_succ]
      ring
    have hh := (hp.pow_dvd_iff_le_factorization hL0).mp hd
    rw [heL] at hh
    omega
  have hcop : c.Coprime (p^(f-e)) :=
    ((hp.coprime_iff_not_dvd.mpr hpc).symm).pow_right _
  obtain ⟨x,hx⟩ := hpriv i
  have hbx : ((p^e : ℕ) : ℤ) ∣ b-x := by
    rw [← hi]
    convert hb.sub hx.1 using 1 <;> ring
  obtain ⟨k,hk⟩ := hbx
  obtain ⟨t,z,hz⟩ := affine_parameter hcop k
  refine ⟨x+(L : ℤ)*t,private_add_step m a hpriv i L hiL hL hx t,z,?_⟩
  have hLcast : (L : ℤ)=(p : ℤ)^e*(c : ℤ) := by exact_mod_cast hc
  simp only [Nat.cast_pow] at hk hz ⊢
  calc
    x+(L : ℤ)*t-b = (p : ℤ)^e*((c : ℤ)*t-k) := by
      rw [hLcast]
      linear_combination -hk
    _ = ((p : ℤ)^e*(p : ℤ)^(f-e))*z := by rw [hz]; ring
    _ = (p : ℤ)^f*z := by rw [← pow_add, Nat.add_sub_of_le hef]

#print axioms every_finer_residue
#print axioms disjoint_of_dvd
#print axioms private_add_step
#print axioms exists_pure_step
#print axioms private_escape_finer
end Erdos7PurePowerPrivatePeriod
