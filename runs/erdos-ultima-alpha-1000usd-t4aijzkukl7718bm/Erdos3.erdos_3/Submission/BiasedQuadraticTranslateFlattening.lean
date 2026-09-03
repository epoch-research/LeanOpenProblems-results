import Submission.WindowBiasLocalization

/-! Polarization is unchanged under admissible translations. Combining this
fact with local bias transfer gives flattening on a translated inner window.
All cube vertices, boundary losses, and divisions by bias are explicit. -/
namespace Erdos3BiasedQuadraticTranslateFlattening
open Finset Erdos3WindowBiasLocalization Erdos3BiasedPolarizationFlattening
  Erdos3LocalQuadraticPolarization Erdos3LocalQuadraticProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3CorrelationSifting Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G]

/-- Translation invariance of polarization follows from the third derivative
identity only when the connecting cube is contained in the local domain. -/
lemma localPolar_translate {R : Set G} {q : G → ℂ}
    (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (b h y : G) (h0 : 0 ∈ R) (hh : h ∈ R) (hy : y ∈ R) (hyh : y+h ∈ R)
    (hb : b ∈ R) (hbh : b+h ∈ R) (hby : b+y ∈ R) (hbyh : (b+y)+h ∈ R) :
    localPolar (fun x ↦ q (b+x)) h y = localPolar q h y := by
  have he := hquad 0 h y b h0 (by simpa using hh) (by simpa using hy)
    (by simpa using hyh) (by simpa using hb) (by simpa using hbh)
    (by simpa using hby) (by simpa using hbyh)
  change derivative (derivative q h) y (0+b)*
    conj (derivative (derivative q h) y 0) = 1 at he
  have ht := unit_conj_cancel
    (derivative_norm_one (derivative q h) (derivative_norm_one q hq h) y 0) he
  simp only [one_mul,zero_add] at ht
  simpa only [localPolar,derivative,zero_add,add_zero,add_assoc] using ht

variable [Fintype G] [DecidableEq G]

/-- A local quadratic phase with bias on C and small mixed polarization
between H and B is almost constant on b+B for some b in C. It is also
almost invariant under B-translations throughout b+H. -/
theorem exists_flat_translate (R : Set G) (C H B : Finset G)
    (hC : C.Nonempty) (hH : H.Nonempty)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic R q)
    (hdom : ∀ b ∈ insert 0 C, ∀ x ∈ insert 0 H, ∀ y ∈ insert 0 B, (b+x)+y ∈ R)
    {β a δ κ : ℝ} (hβ : δ < β) (hbias : β ≤ ‖𝔼 x : C, q x‖)
    (hpolar : ∀ x ∈ H, ∀ y ∈ B, ‖localPolar q x y-1‖ ≤ a)
    (hstableC : ∀ x ∈ H, (𝔼 t : G, |normalized C (t+x)-normalized C t|) ≤ δ)
    (hstableH : ∀ y ∈ B, (𝔼 t : G, |normalized H (t+y)-normalized H t|) ≤ κ) :
    ∃ b ∈ C, (∀ y ∈ B, ‖q (b+y)-q b‖ ≤ (a+κ)/(β-δ)) ∧
      ∀ x ∈ H, ∀ y ∈ B, ‖q ((b+x)+y)-q (b+x)‖ ≤ a+(a+κ)/(β-δ) := by
  obtain ⟨b,hb,hbias'⟩ := exists_biased_translate C H hC hH q (fun x ↦ (hq x).le) hbias hstableC
  have hpol (y : G) (hy : y ∈ B) (x : G) (hx : x ∈ H) :
      ‖localPolar (fun z ↦ q (b+z)) x y-1‖ ≤ a := by
    have h0C : (0 : G) ∈ insert 0 C := mem_insert_self _ _
    have h0H : (0 : G) ∈ insert 0 H := mem_insert_self _ _
    have h0B : (0 : G) ∈ insert 0 B := mem_insert_self _ _
    have hbC : b ∈ insert 0 C := mem_insert_of_mem hb
    have hxH : x ∈ insert 0 H := mem_insert_of_mem hx
    have hyB : y ∈ insert 0 B := mem_insert_of_mem hy
    rw [localPolar_translate hq hquad b x y
      (by simpa using hdom 0 h0C 0 h0H 0 h0B)
      (by simpa using hdom 0 h0C x hxH 0 h0B)
      (by simpa using hdom 0 h0C 0 h0H y hyB)
      (by simpa only [zero_add,add_comm x y] using hdom 0 h0C x hxH y hyB)
      (by simpa using hdom b hbC 0 h0H 0 h0B)
      (by simpa using hdom b hbC x hxH 0 h0B)
      (by simpa using hdom b hbC 0 h0H y hyB)
      (by simpa only [add_assoc,add_comm x y] using hdom b hbC x hxH y hyB)]
    exact hpolar x hx y hy
  have hflat (y : G) (hy : y ∈ B) := biased_polarization_flattening H hH
    (fun z ↦ q (b+z)) (fun z ↦ hq (b+z)) y (sub_pos.mpr hβ) hbias'
    (hpol y hy) (hstableH y hy)
  refine ⟨b,hb,?_,?_⟩
  · intro y hy
    simpa only [add_zero] using (hflat y hy).1
  · intro x hx y hy
    simpa only [add_assoc] using (hflat y hy).2 x hx

/-- A Bohr-domain version with a single radius budget replacing the eight
cube-domain hypotheses. -/
theorem exists_flat_bohr_translate (D : Finset (AddChar G ℂ))
    {R r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : r+s+t ≤ R)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1) (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    (B : Finset G) (hB : B ⊆ bohr D t)
    {β a δ κ : ℝ} (hβ : δ < β) (hbias : β ≤ ‖𝔼 x : bohr D r, q x‖)
    (hpolar : ∀ x ∈ bohr D s, ∀ y ∈ B, ‖localPolar q x y-1‖ ≤ a)
    (hstableC : ∀ x ∈ bohr D s,
      (𝔼 u : G, |normalized (bohr D r) (u+x)-normalized (bohr D r) u|) ≤ δ)
    (hstableH : ∀ y ∈ B,
      (𝔼 u : G, |normalized (bohr D s) (u+y)-normalized (bohr D s) u|) ≤ κ) :
    ∃ b ∈ bohr D r, (∀ y ∈ B, ‖q (b+y)-q b‖ ≤ (a+κ)/(β-δ)) ∧
      ∀ x ∈ bohr D s, ∀ y ∈ B, ‖q ((b+x)+y)-q (b+x)‖ ≤ a+(a+κ)/(β-δ) := by
  apply exists_flat_translate (bohr D R : Set G) (bohr D r) (bohr D s) B
    ⟨0,bohr_zero D hr⟩ ⟨0,bohr_zero D hs⟩ q hq hquad ?_ hβ hbias hpolar hstableC hstableH
  intro b hb x hx y hy
  have hb' : b ∈ bohr D r := by simpa only [insert_eq_of_mem (bohr_zero D hr)] using hb
  have hx' : x ∈ bohr D s := by simpa only [insert_eq_of_mem (bohr_zero D hs)] using hx
  have hy' : y ∈ bohr D t := by
    rcases mem_insert.mp hy with rfl | hy
    · exact bohr_zero D ht
    · exact hB hy
  exact bohr_mono D hR (bohr_add (bohr_add hb' hx') hy')

#print axioms localPolar_translate
#print axioms exists_flat_translate
#print axioms exists_flat_bohr_translate
end Erdos3BiasedQuadraticTranslateFlattening
