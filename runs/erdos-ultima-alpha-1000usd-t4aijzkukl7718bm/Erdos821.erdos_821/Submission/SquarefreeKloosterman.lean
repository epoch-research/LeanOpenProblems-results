import Submission.KloostermanRingProducts

/-!
# Elementary Kloosterman bounds for squarefree moduli

The Chinese remainder theorem transfers the finite-field estimate. A gcd
factor is retained for nonunit second frequencies; it cannot be discarded
in the subsequent completion argument.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman

section PiField
variable {I : Type*} [Fintype I] (F : I → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

lemma ringKloosterman_pi_fourth (ψ : AddChar (∀ i, F i) ℂ) (hψ : ψ.IsPrimitive)
    (a b : ∀ i, F i) :
    ‖ringKloosterman ψ a b‖^4 ≤
      (3 : ℝ)^(Fintype.card I) * (∏ i : I, (Fintype.card (F i) : ℝ))^3 *
        ∏ i : I, if b i=0 then (Fintype.card (F i) : ℝ) else 1 := by
  rw [ringKloosterman_pi F, norm_prod, ← Finset.prod_pow]
  calc
    _ ≤ ∏ i : I, 3*(Fintype.card (F i) : ℝ)^3*
        (if b i=0 then (Fintype.card (F i) : ℝ) else 1) := by
      apply prod_le_prod (fun i _ => by positivity)
      intro i _
      exact ringKloosterman_fourth_field _ (primitive_coordinate F ψ hψ i) (a i) (b i)
    _ = _ := by
      simp only [prod_mul_distrib, prod_pow, prod_const, card_univ]

end PiField

noncomputable def squarefreeCRT (q : ℕ) (hq : Squarefree q) :
    ZMod q ≃+* ∀ p : q.primeFactors, ZMod (p : ℕ) := by
  have hprod : (∏ p : q.primeFactors, (p : ℕ))=q := by
    exact (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hq)
  have hcop : Pairwise (fun p r : q.primeFactors => (p : ℕ).Coprime (r : ℕ)) := by
    intro p r hne
    apply (Nat.coprime_primes (Nat.mem_primeFactors.mp p.property).1
      (Nat.mem_primeFactors.mp r.property).1).mpr
    exact fun he => hne (Subtype.ext he)
  exact (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi (fun p : q.primeFactors => (p : ℕ)) hcop)

lemma squarefreeCRT_apply (q : ℕ) (hq : Squarefree q) (b : ZMod q) (p : q.primeFactors) :
    squarefreeCRT q hq b p = (b.val : ZMod (p : ℕ)) := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hb : (b.val : ZMod q)=b := ZMod.natCast_zmod_val b
  calc
    _ = squarefreeCRT q hq (b.val : ZMod q) p := by rw [hb]
    _ = _ := by rw [map_natCast]; rfl

noncomputable def annihilatorPrimeProduct (q b : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => p ∣ b), p

lemma annihilatorPrimeProduct_dvd_gcd (q b : ℕ) (hq : q ≠ 0) :
    annihilatorPrimeProduct q b ∣ Nat.gcd b q := by
  have hg : Nat.gcd b q ≠ 0 := Nat.gcd_ne_zero_right hq
  have hsub : q.primeFactors.filter (fun p => p ∣ b) ⊆ (Nat.gcd b q).primeFactors := by
    intro p hp
    obtain ⟨hp,hpb⟩ := mem_filter.mp hp
    obtain ⟨hpr,hpq,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpr,Nat.dvd_gcd hpb hpq,hg⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans (Nat.prod_primeFactors_dvd _)

lemma annihilatorPrimeProduct_le_gcd (q b : ℕ) (hq : q ≠ 0) :
    annihilatorPrimeProduct q b ≤ Nat.gcd b q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right hq))
    (annihilatorPrimeProduct_dvd_gcd q b hq)

/-- A three-quarter-power bound with the gcd loss required at nonunit
frequencies. The additive character may be any primitive one. -/
theorem ringKloosterman_squarefree_fourth (q : ℕ) [NeZero q] (hq : Squarefree q)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (a b : ZMod q) :
    ‖ringKloosterman ψ a b‖^4 ≤
      (3 : ℝ)^q.primeFactors.card*(q : ℝ)^3*(Nat.gcd b.val q : ℕ) := by
  let P := q.primeFactors
  letI : DecidableEq P := fun a b => Classical.propDecidable (a=b)
  let F : P → Type := fun p => ZMod (p : ℕ)
  letI (p : P) : DecidableEq (F p) := fun a b => Classical.propDecidable (a=b)
  letI (p : P) : Fact (p : ℕ).Prime := ⟨(Nat.mem_primeFactors.mp p.property).1⟩
  let e := squarefreeCRT q hq
  let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hψ' : ψ'.IsPrimitive := primitive_transport e.symm ψ hψ
  have he : ringKloosterman ψ a b = ringKloosterman ψ' (e a) (e b) := by
    simpa only [RingEquiv.symm_apply_apply] using (ringKloosterman_equiv e.symm ψ (e a) (e b)).symm
  have hh := ringKloosterman_pi_fourth F ψ' hψ' (e a) (e b)
  have hcard : Fintype.card P = q.primeFactors.card := Fintype.card_coe _
  have hprod : (∏ p : P, (Fintype.card (F p) : ℝ))=(q : ℝ) := by
    simp only [F, ZMod.card, ← Nat.cast_prod]
    congr 1
    exact (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p)).trans
      (Nat.prod_primeFactors_of_squarefree hq)
  have hbad : (∏ p : P, if e b p=0 then (Fintype.card (F p) : ℝ) else 1) =
      (annihilatorPrimeProduct q b.val : ℝ) := by
    simp only [e, squarefreeCRT_apply, F, ZMod.card, ZMod.natCast_eq_zero_iff,
      annihilatorPrimeProduct, Nat.cast_prod, Nat.cast_ite, Nat.cast_one,
      P, prod_filter]
    exact Finset.prod_coe_sort q.primeFactors
      (fun p : ℕ => if p ∣ b.val then (p : ℝ) else 1)
  rw [← he, hcard, hprod, hbad] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast annihilatorPrimeProduct_le_gcd q b.val (NeZero.ne q)) (by positivity))

end Erdos821.Kloosterman
