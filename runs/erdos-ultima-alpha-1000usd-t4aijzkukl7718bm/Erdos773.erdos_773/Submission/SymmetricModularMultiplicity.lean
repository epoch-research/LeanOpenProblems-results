import Submission.SymmetricSquareAlteration

/-! Symmetric integer square-Sidon sets can have polynomially large modular
sum multiplicity at their prime reflection modulus. This does not settle
Erdos 773: the integer Sidon exponent used here remains below two thirds. -/
namespace Erdos773.SymmetricModularMultiplicity
open Finset Filter
set_option maxHeartbeats 1000000
set_option Elab.async false

noncomputable def residues (p : ℕ) (C : Finset ℕ) : Finset (ZMod p) :=
  C.image (fun n : ℕ => (n : ZMod p)^2)

noncomputable def orderedReps (p : ℕ) (R : Finset (ZMod p)) (r : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  (R ×ˢ R).filter (fun xy => xy.1+xy.2=r)

lemma square_image_card {F : Type*} [Field F] [DecidableEq F] (A : Finset F) :
    A.card ≤ 2*(A.image (fun a => a^2)).card := by
  classical
  apply card_le_mul_card_image A 2
  intro r hr
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hr
  have hsub : A.filter (fun x => x^2=a^2) ⊆ {a,-a} := by
    intro x hx
    have he := sq_eq_sq_iff_eq_or_eq_neg.mp (mem_filter.mp hx).2
    simpa only [mem_insert,mem_singleton] using he
  exact (card_le_card hsub).trans card_le_two

lemma root_card_bound {p : ℕ} (hp : p.Prime) (C : Finset ℕ)
    (hC : ∀ a ∈ C, a < p) : C.card ≤ 2*(residues p C).card := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hi : Set.InjOn (fun a : ℕ => (a : ZMod p)) C := by
    intro a ha b hb he
    exact ((ZMod.natCast_eq_natCast_iff a b p).mp he).eq_of_lt_of_lt (hC a ha) (hC b hb)
  have hh := square_image_card (C.image (fun a : ℕ => (a : ZMod p)))
  simpa only [card_image_of_injOn hi,image_image,Function.comp_def,residues] using hh

lemma exists_large_sum_fiber {p : ℕ} (hp : 0 < p) (R : Finset (ZMod p)) :
    ∃ r : ZMod p, R.card^2 ≤ p*(orderedReps p R r).card := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨r,hr,hmax⟩ := exists_max_image (univ : Finset (ZMod p))
    (fun r => (orderedReps p R r).card) univ_nonempty
  refine ⟨r,?_⟩
  calc
    _ = (R ×ˢ R).card := by simp [pow_two]
    _ = ∑ r : ZMod p, (orderedReps p R r).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _r : ZMod p, (orderedReps p R r).card :=
      sum_le_sum (fun x hx => hmax x hx)
    _ = _ := by simp [ZMod.card]

/-- This finite count uses only prime-field two-to-one squaring and pigeonhole. -/
theorem finite_modular_multiplicity {p : ℕ} (hp : p.Prime) (C : Finset ℕ)
    (hC : ∀ a ∈ C, a < p) :
    ∃ r : ZMod p, C.card^2 ≤ 4*p*(orderedReps p (residues p C) r).card := by
  obtain ⟨r,hr⟩ := exists_large_sum_fiber hp.pos (residues p C)
  have hc := root_card_bound hp C hC
  have hs := Nat.pow_le_pow_left hc 2
  refine ⟨r,?_⟩
  nlinarith only [hs,hr]

/-- Arbitrarily close to the two-thirds exponent, symmetry and integer
Sidonness coexist with modular ordered-sum multiplicity at least p^(1/3-epsilon).
The representations here use distinct residue VALUES, not fourfold root lifts. -/
theorem eventual_prime_multiplicity (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∃ C ⊆ Icc 1 p,
      (∀ a ∈ C, a ≤ p ∧ p-a ∈ C) ∧
      IsSidon (C.image (fun n => n^2) : Set ℕ) ∧
      (p : ℝ)^(2/3-ε/4) ≤ (C.card : ℝ) ∧
      ∃ r : ZMod p, (p : ℝ)^(1/3-ε) ≤
        ((orderedReps p (residues p C) r).card : ℝ) := by
  have hlarge : ∀ᶠ p : ℕ in atTop, 4 ≤ (p : ℝ)^(ε/2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε/2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop)).eventually_ge_atTop 4
  filter_upwards [SymmetricSquareAlteration.eventual_symmetric_lower (ε/4) (by positivity),
    hlarge,eventually_ge_atTop 1] with p hC hlarge hp1
  intro hp
  obtain ⟨C,hC,hSym,hSid,hcard⟩ := hC
  have hlt : ∀ a ∈ C, a < p := by
    intro a ha
    have hpa := (hSym a ha).1
    have hpos := (mem_Icc.mp (hC (hSym a ha).2)).1
    omega
  obtain ⟨r,hr⟩ := finite_modular_multiplicity hp C hlt
  refine ⟨C,hC,hSym,hSid,hcard,r,?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr' : (C.card : ℝ)^2 ≤ 4*(p : ℝ)*(orderedReps p (residues p C) r).card := by
    exact_mod_cast hr
  have hsq : ((p : ℝ)^(2/3-ε/4))^2 ≤ (C.card : ℝ)^2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hcard 2
  have hid : ((p : ℝ)^(2/3-ε/4))^2 =
      (p : ℝ)^(ε/2)*p*(p : ℝ)^(1/3-ε) := by
    rw [← Real.rpow_mul_natCast hp0.le]
    conv_rhs => lhs; rhs; rw [← Real.rpow_one (p : ℝ)]
    rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    norm_num
    ring
  have hlo : 4*(p : ℝ)*(p : ℝ)^(1/3-ε) ≤ ((p : ℝ)^(2/3-ε/4))^2 := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlarge hp0.le) (Real.rpow_nonneg hp0.le _)
  nlinarith only [hlo,hsq,hr',hp0]

lemma sidon_ordered_capacity {p : ℕ} (R : Finset (ZMod p))
    (hR : IsSidon (R : Set (ZMod p))) (r : ZMod p) :
    (orderedReps p R r).card ≤ 2 := by
  classical
  by_cases hn : (orderedReps p R r).Nonempty
  · obtain ⟨ab,hab⟩ := hn
    obtain ⟨habR,habr⟩ := mem_filter.mp hab
    have hsub : orderedReps p R r ⊆ {ab,(ab.2,ab.1)} := by
      intro cd hcd
      obtain ⟨hcdR,hcdr⟩ := mem_filter.mp hcd
      obtain hh | hh := hR cd.1 (mem_product.mp hcdR).1 ab.1 (mem_product.mp habR).1
        cd.2 (mem_product.mp hcdR).2 ab.2 (mem_product.mp habR).2 (hcdr.trans habr.symm)
      · exact mem_insert.mpr (Or.inl (Prod.ext hh.1 hh.2))
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext hh.1 hh.2)))
    exact (card_le_card hsub).trans card_le_two
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp


/-- The quantitative modular-multiplicity witnesses occur at unbounded primes. -/
theorem unbounded_prime_multiplicity (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ ∃ C ⊆ Icc 1 p,
      (∀ a ∈ C, a ≤ p ∧ p-a ∈ C) ∧
      IsSidon (C.image (fun n => n^2) : Set ℕ) ∧
      (p : ℝ)^(2/3-ε/4) ≤ (C.card : ℝ) ∧
      ∃ r : ZMod p, (p : ℝ)^(1/3-ε) ≤
        ((orderedReps p (residues p C) r).card : ℝ) := by
  obtain ⟨P,hP⟩ := eventually_atTop.mp (eventual_prime_multiplicity ε hε)
  obtain ⟨p,hpB,hp⟩ := Nat.exists_infinite_primes (max P (M+1))
  exact ⟨p,by omega,hp,hP p (by omega) hp⟩

/-- For every exponent loss below one third, the displayed modular multiplicity
also certifies actual failure of modular Sidonness. -/
theorem eventual_prime_nonsidon (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/3) :
    ∀ᶠ p : ℕ in atTop, p.Prime → ∃ C ⊆ Icc 1 p,
      (∀ a ∈ C, a ≤ p ∧ p-a ∈ C) ∧
      IsSidon (C.image (fun n => n^2) : Set ℕ) ∧
      (p : ℝ)^(2/3-ε/4) ≤ (C.card : ℝ) ∧
      ¬ IsSidon (residues p C : Set (ZMod p)) := by
  have ht : ∀ᶠ p : ℕ in atTop, 2 < (p : ℝ)^(1/3-ε) :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1/3-ε)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop)).eventually_gt_atTop 2
  filter_upwards [eventual_prime_multiplicity ε hε,ht] with p hp hlarge
  intro hprime
  obtain ⟨C,hC,hSym,hSid,hcard,r,hr⟩ := hp hprime
  refine ⟨C,hC,hSym,hSid,hcard,?_⟩
  intro hmod
  have hh : ((orderedReps p (residues p C) r).card : ℝ) ≤ 2 := by
    exact_mod_cast sidon_ordered_capacity (residues p C) hmod r
  linarith only [hr,hh,hlarge]

end Erdos773.SymmetricModularMultiplicity

#print axioms Erdos773.SymmetricModularMultiplicity.finite_modular_multiplicity
#print axioms Erdos773.SymmetricModularMultiplicity.eventual_prime_multiplicity
#print axioms Erdos773.SymmetricModularMultiplicity.sidon_ordered_capacity

#print axioms Erdos773.SymmetricModularMultiplicity.unbounded_prime_multiplicity
#print axioms Erdos773.SymmetricModularMultiplicity.eventual_prime_nonsidon
