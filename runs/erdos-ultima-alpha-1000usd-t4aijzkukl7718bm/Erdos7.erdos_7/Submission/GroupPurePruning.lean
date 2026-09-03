import Submission.PureCofactorPruning

/-! Arithmetic facts underlying a restricted fresh-pure group search.
No normalization theorem for arbitrary covering systems is asserted. -/
namespace Erdos7GroupPurePruning
set_option autoImplicit false

/-- A pure divisor class meeting one aligned member covers every aligned
member's entire cofactor slice, independently of the surviving core masks. -/
theorem covers_coherent_family {I : Type*} (m d : ℕ) (b : I → ℤ)
    (hd : d ∣ m) (hcoh : ∀ i j, (d : ℤ) ∣ b i - b j)
    (i₀ : I) (r : ℤ) (h : (d : ℤ) ∣ b i₀ - r) :
    ∀ i x, (m : ℤ) ∣ x - b i → (d : ℤ) ∣ x - r := by
  intro i x hx
  have hdm : (d : ℤ) ∣ m := by exact_mod_cast hd
  have hh := dvd_add (dvd_add (hdm.trans hx) (hcoh i i₀)) h
  simpa only [sub_add_sub_cancel] using hh

/-- A common shift divisible by d supplies the alignment hypothesis. -/
theorem covers_shifted_family {I : Type*} (m d : ℕ) (b : I → ℤ)
    (K : ℤ) (hd : d ∣ m) (hK : (d : ℤ) ∣ K)
    (hb : ∀ i j, K ∣ b i - b j) (i₀ : I) (r : ℤ)
    (h : (d : ℤ) ∣ b i₀ - r) :
    ∀ i x, (m : ℤ) ∣ x - b i → (d : ℤ) ∣ x - r := by
  exact covers_coherent_family m d b hd (fun i j => hK.trans (hb i j)) i₀ r h

/-- If p divides both the cofactor slices and the class modulus, the class
cannot meet two different first-p fibres. -/
theorem not_meets_two_fibres (p m d : ℕ) (hpm : p ∣ m) (hpd : p ∣ d)
    (b c r : ℤ) (hne : ¬ (p : ℤ) ∣ b - c) :
    ¬ ((∃ x : ℤ, (m : ℤ) ∣ x - b ∧ (d : ℤ) ∣ x - r) ∧
       (∃ y : ℤ, (m : ℤ) ∣ y - c ∧ (d : ℤ) ∣ y - r)) := by
  rintro ⟨⟨x, hxm, hxd⟩, ⟨y, hym, hyd⟩⟩
  have hm : (p : ℤ) ∣ m := by exact_mod_cast hpm
  have hd : (p : ℤ) ∣ d := by exact_mod_cast hpd
  have hb : (p : ℤ) ∣ b - r := by
    have hh := dvd_sub (hd.trans hxd) (hm.trans hxm)
    convert hh using 1 <;> ring
  have hc : (p : ℤ) ∣ c - r := by
    have hh := dvd_sub (hd.trans hyd) (hm.trans hym)
    convert hh using 1 <;> ring
  apply hne
  have hh := dvd_sub hb hc
  convert hh using 1 <;> ring

lemma full_last_prime_controls :
    ¬ Nat.Coprime 2 (20/2) ∧ ¬ Nat.Coprime 2 (20/10) ∧
    Nat.Coprime 2 (20/4) ∧ Nat.Coprime 2 (20/20) ∧
    Nat.Coprime 7 (140/35) ∧ Nat.Coprime 7 (140/70) ∧
    Nat.Coprime 7 (140/140) ∧ ¬ Nat.Coprime 7 (140/20) := by
  decide +kernel

#print axioms covers_coherent_family
#print axioms covers_shifted_family
#print axioms not_meets_two_fibres
#print axioms full_last_prime_controls
end Erdos7GroupPurePruning
