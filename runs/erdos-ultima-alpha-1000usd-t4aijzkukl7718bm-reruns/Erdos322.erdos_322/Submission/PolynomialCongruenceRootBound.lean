import Submission.DivisorBound

/-!
Uniform congruence-root bounds for a fixed monic polynomial with a nonzero
integer Bezout constant for its derivative. These are modular root bounds,
not bounds for the unrestricted quartic representation count.
-/
namespace Erdos322Research.PolynomialCongruenceRootBound

open Polynomial Finset
set_option Elab.async false

/-- The integer representatives of the roots modulo `n`. -/
def rootsMod (f : ℤ[X]) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => (n : ℤ) ∣ f.eval (a : ℤ))

lemma mem_rootsMod {f : ℤ[X]} {n a : ℕ} :
    a ∈ rootsMod f n ↔ a < n ∧ (n : ℤ) ∣ f.eval (a : ℤ) := by
  simp [rootsMod]

private lemma eval_mod (f : ℤ[X]) {n a : ℕ}
    (h : (n : ℤ) ∣ f.eval (a : ℤ)) :
    (n : ℤ) ∣ f.eval ((a % n : ℕ) : ℤ) := by
  have he : (a : ℤ) - ((a % n : ℕ) : ℤ) = (n : ℤ) * (a / n : ℕ) := by
    have hh : ((a % n : ℕ) : ℤ) + (n : ℤ) * ((a / n : ℕ) : ℤ) = a := by
      exact_mod_cast Nat.mod_add_div a n
    linarith
  have hd := f.sub_dvd_eval_sub (a : ℤ) ((a % n : ℕ) : ℤ)
  have hd' : (n : ℤ) ∣ f.eval (a : ℤ) - f.eval ((a % n : ℕ) : ℤ) :=
    dvd_trans ⟨_, he⟩ hd
  convert dvd_sub h hd' using 1; ring

/-- A single prime-power residue ball has uniformly bounded root fibers. -/
theorem same_ball_roots {p e δ : ℕ} [Fact p.Prime]
    (f A B : ℤ[X]) (C : ℤ)
    (hbez : A*f+B*f.derivative = Polynomial.C C)
    (hC : ¬(p : ℤ)^(δ+1) ∣ C) (he : δ < e)
    (a b : ℤ) (ha : (p : ℤ)^e ∣ f.eval a) (hb : (p : ℤ)^e ∣ f.eval b)
    (hab : (p : ℤ)^(δ+1) ∣ b-a) :
    (p : ℤ)^(e-δ) ∣ b-a := by
  have hder : ¬(p : ℤ)^(δ+1) ∣ f.derivative.eval a := by
    intro hd
    apply hC
    have hp : (p : ℤ)^(δ+1) ∣ (p : ℤ)^e := pow_dvd_pow _ (by omega)
    have hx := congrArg (Polynomial.eval a) hbez
    simp only [eval_add, eval_mul, eval_C] at hx
    rw [← hx]
    exact dvd_add (dvd_mul_of_dvd_right (hp.trans ha) _) (dvd_mul_of_dvd_right hd _)
  have hd0 : f.derivative.eval a ≠ 0 := by
    intro h; exact hder (h ▸ dvd_zero _)
  let v := padicValInt p (f.derivative.eval a)
  have hv : v ≤ δ := by
    have hh := (padicValInt_dvd_iff (p := p) (δ+1) (f.derivative.eval a)).not.mp hder
    dsimp [v]
    omega
  by_cases hba : b-a=0
  · rw [hba]; exact dvd_zero _
  obtain ⟨q,hq⟩ := f.binomExpansion a (b-a)
  rw [add_sub_cancel] at hq
  let u := f.derivative.eval a + q*(b-a)
  have hprod : (p : ℤ)^e ∣ u*(b-a) := by
    have hh := dvd_sub hb ha
    convert hh using 1
    dsimp [u]
    linear_combination -hq
  have hqv : (p : ℤ)^(v+1) ∣ q*(b-a) := by
    exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega : v+1 ≤ δ+1)).trans hab) _
  have hu_not : ¬(p : ℤ)^(v+1) ∣ u := by
    intro hu
    have hd := dvd_sub hu hqv
    have hd' : (p : ℤ)^(v+1) ∣ f.derivative.eval a := by
      simpa [u] using hd
    have hh := (padicValInt_dvd_iff (p := p) (v+1) (f.derivative.eval a)).mp hd'
    rcases hh with hh | hh
    · exact hd0 hh
    · change v+1 ≤ v at hh
      omega
  have hu0 : u ≠ 0 := by intro h; exact hu_not (h ▸ dvd_zero _)
  have huv : padicValInt p u ≤ v := by
    have hh := (padicValInt_dvd_iff (p := p) (v+1) u).not.mp hu_not
    omega
  have hm : e ≤ padicValInt p (u*(b-a)) :=
    ((padicValInt_dvd_iff (p := p) e (u*(b-a))).mp hprod).resolve_left
      (mul_ne_zero hu0 hba)
  rw [padicValInt.mul hu0 hba] at hm
  apply (padicValInt_dvd_iff (p := p) (e-δ) (b-a)).mpr
  exact Or.inr (by omega)

lemma field_roots_bound (f : ℤ[X]) (hf : f.Monic) (p : ℕ) [Fact p.Prime] :
    (rootsMod f p).card ≤ f.natDegree := by
  classical
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := (hf.map _).ne_zero
  have hi : Set.InjOn (fun a : ℕ => (a : ZMod p)) (rootsMod f p) := by
    intro a ha b hb h
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp h |>.eq_of_lt_of_lt
      (mem_rootsMod.mp ha).1 (mem_rootsMod.mp hb).1
  have hh := Finset.card_le_card_of_injOn (fun a : ℕ => (a : ZMod p))
    (s := rootsMod f p) (t := F.roots.toFinset) (by
      intro a ha
      change (a : ZMod p) ∈ F.roots.toFinset
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hF]
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (f.eval (a : ℤ)) p).mpr
        (mem_rootsMod.mp ha).2
      change F.eval (a : ZMod p)=0
      rw [Polynomial.eval_map]
      have hcast : (Int.castRingHom (ZMod p)) (a : ℤ) = (a : ZMod p) := by simp
      rw [← hcast, Polynomial.eval₂_at_apply]
      exact hz) hi
  exact hh.trans ((Multiset.toFinset_card_le _).trans
    (Polynomial.card_roots' _ |>.trans Polynomial.natDegree_map_le))

lemma prime_power_bound_aux (f A B : ℤ[X]) (hf : f.Monic) (C : ℤ)
    (hbez : A*f+B*f.derivative = Polynomial.C C)
    (p e δ : ℕ) [Fact p.Prime] (hC : ¬(p : ℤ)^(δ+1) ∣ C)
    (he : δ < e) :
    (rootsMod f (p^e)).card ≤ f.natDegree * (p^δ)^2 := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpow : p^(e-δ)*p^δ=p^e := by rw [← pow_add, Nat.sub_add_cancel he.le]
  have hpow' : p^(δ+1)=p^δ*p := pow_succ _ _
  let code (a : ℕ) := (a % p, (a % p^(δ+1) / p, a / p^(e-δ)))
  have hcard := Finset.card_le_card_of_injOn code
    (s := rootsMod f (p^e))
    (t := rootsMod f p ×ˢ (Finset.range (p^δ) ×ˢ Finset.range (p^δ))) (by
      intro a ha
      obtain ⟨hal, had⟩ := mem_rootsMod.mp ha
      have hpdiv : p ∣ p^e := dvd_pow_self p (by omega)
      have hpdivz : (p : ℤ) ∣ ((p^e : ℕ) : ℤ) := by exact_mod_cast hpdiv
      refine Finset.mem_product.mpr ⟨mem_rootsMod.mpr
        ⟨Nat.mod_lt _ hp, eval_mod f (hpdivz.trans had)⟩, ?_⟩
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        apply (Nat.div_lt_iff_lt_mul hp).mpr
        rw [← hpow']
        exact Nat.mod_lt _ (pow_pos hp _)
      · apply Finset.mem_range.mpr
        apply (Nat.div_lt_iff_lt_mul (pow_pos hp _)).mpr
        rwa [mul_comm, hpow]) (by
      intro a ha b hb hc
      have h0 := congrArg Prod.fst hc
      have h1 := congrArg (fun q : ℕ × (ℕ × ℕ) => q.2.1) hc
      have h2 := congrArg (fun q : ℕ × (ℕ × ℕ) => q.2.2) hc
      dsimp only [code] at h0 h1 h2
      obtain ⟨hal,had⟩ := mem_rootsMod.mp ha
      obtain ⟨hbl,hbd⟩ := mem_rootsMod.mp hb
      have hball : a % p^(δ+1) = b % p^(δ+1) := by
        have hd : p ∣ p^(δ+1) := dvd_pow_self _ (by omega)
        have ha' := Nat.mod_add_div (a % p^(δ+1)) p
        have hb' := Nat.mod_add_div (b % p^(δ+1)) p
        rw [Nat.mod_mod_of_dvd _ hd] at ha' hb'
        rw [h0, h1] at ha'
        omega
      have hab : (p : ℤ)^(δ+1) ∣ (b : ℤ)-a := by
        have hh := Nat.modEq_iff_dvd.mp hball
        simpa only [Nat.cast_pow] using hh
      have hsep := same_ball_roots f A B C hbez hC he
        (a : ℤ) (b : ℤ) (by simpa only [Nat.cast_pow] using had)
        (by simpa only [Nat.cast_pow] using hbd) hab
      have hmod : a % p^(e-δ)=b % p^(e-δ) := by
        apply Nat.modEq_iff_dvd.mpr
        simpa only [Nat.cast_pow] using hsep
      have ha' := Nat.mod_add_div a (p^(e-δ))
      have hb' := Nat.mod_add_div b (p^(e-δ))
      rw [hmod, h2] at ha'
      omega)
  simp only [Finset.card_product, Finset.card_range] at hcard
  simpa only [pow_two] using hcard.trans
    (Nat.mul_le_mul_right _ (field_roots_bound f hf p))

lemma rootsMod_card_le (f : ℤ[X]) (n : ℕ) : (rootsMod f n).card ≤ n := by
  simpa [rootsMod] using Finset.card_filter_le (s := Finset.range n)
    (p := fun a => (n : ℤ) ∣ f.eval (a : ℤ))

lemma prime_power_bound (f A B : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (C : ℕ) (hC : 0 < C) (hbez : A*f+B*f.derivative = Polynomial.C (C : ℤ))
    (p e : ℕ) [Fact p.Prime] :
    (rootsMod f (p^e)).card ≤ f.natDegree * (Nat.gcd (p^e) C)^2 := by
  let δ := padicValNat p C
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hδC : p^δ ∣ C := pow_padicValNat_dvd
  by_cases he : e ≤ δ
  · have heC : p^e ∣ C := (pow_dvd_pow _ he).trans hδC
    rw [Nat.gcd_eq_left heC]
    apply (rootsMod_card_le f _).trans
    have hn : 0 < p^e := pow_pos hp _
    nlinarith
  · have hh : ¬(p : ℤ)^(δ+1) ∣ (C : ℤ) := by
      have h := pow_succ_padicValNat_not_dvd (p := p) hC.ne'
      exact_mod_cast h
    have hroot := prime_power_bound_aux f A B hf (C : ℤ) hbez p e δ hh (by omega)
    apply hroot.trans
    have hgdiv : p^δ ∣ Nat.gcd (p^e) C := Nat.dvd_gcd
      (pow_dvd_pow _ (by omega)) hδC
    have hgpos : 0 < Nat.gcd (p^e) C := Nat.gcd_pos_of_pos_left _ (pow_pos hp _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_of_dvd hgpos hgdiv) 2)

lemma rootsMod_coprime_mul_le (f : ℤ[X]) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    (rootsMod f (m*n)).card ≤ (rootsMod f m).card * (rootsMod f n).card := by
  classical
  have hh := Finset.card_le_card_of_injOn (fun a : ℕ => (a%m, a%n))
    (s := rootsMod f (m*n)) (t := rootsMod f m ×ˢ rootsMod f n) (by
      intro a ha
      have hd := (mem_rootsMod.mp ha).2
      have hdm : (m : ℤ) ∣ ((m*n : ℕ) : ℤ) := by
        exact_mod_cast (dvd_mul_right m n)
      have hdn : (n : ℤ) ∣ ((m*n : ℕ) : ℤ) := by
        exact_mod_cast (dvd_mul_left n m)
      exact Finset.mem_product.mpr ⟨mem_rootsMod.mpr
        ⟨Nat.mod_lt _ hm, eval_mod f (hdm.trans hd)⟩, mem_rootsMod.mpr
        ⟨Nat.mod_lt _ hn, eval_mod f (hdn.trans hd)⟩⟩) (by
      intro a ha b hb h
      have hc : a ≡ b [MOD m*n] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      exact hc.eq_of_lt_of_lt (mem_rootsMod.mp ha).1 (mem_rootsMod.mp hb).1)
  simpa only [Finset.card_product] using hh

/-- The bad-prime contribution is absorbed by the square of a fixed Bezout
constant; the remaining dependence is a fixed power of the divisor count. -/
theorem rootsMod_divisor_bound (f A B : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (C : ℕ) (hC : 0 < C)
    (hbez : A*f+B*f.derivative = Polynomial.C (C : ℤ)) (n : ℕ) :
    (rootsMod f n).card ≤ n.divisors.card^f.natDegree * (Nat.gcd n C)^2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [rootsMod]
  | one => simp [rootsMod]
  | prime_pow p e hp he =>
    letI : Fact p.Prime := ⟨hp⟩
    have hb := prime_power_bound f A B hf hd C hC hbez p e
    have hd' : f.natDegree ≤ (e+1)^f.natDegree := by
      exact (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left (by omega) _)
    apply hb.trans
    apply Nat.mul_le_mul_right
    simpa only [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range] using hd'
  | coprime a b ha hb hab ia ib =>
    have hgd : Nat.gcd a C * Nat.gcd b C ∣ Nat.gcd (a*b) C := by
      apply Nat.dvd_gcd
      · exact mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
      · exact (Nat.Coprime.of_dvd (Nat.gcd_dvd_left _ _)
          (Nat.gcd_dvd_left _ _) hab).mul_dvd_of_dvd_of_dvd
          (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    have hgle : Nat.gcd a C * Nat.gcd b C ≤ Nat.gcd (a*b) C :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by positivity)) hgd
    calc
      (rootsMod f (a*b)).card ≤ (rootsMod f a).card * (rootsMod f b).card :=
        rootsMod_coprime_mul_le f a b (by omega) (by omega) hab
      _ ≤ (a.divisors.card^f.natDegree*(Nat.gcd a C)^2) *
          (b.divisors.card^f.natDegree*(Nat.gcd b C)^2) := Nat.mul_le_mul ia ib
      _ = (a*b).divisors.card^f.natDegree * (Nat.gcd a C * Nat.gcd b C)^2 := by
        rw [hab.card_divisors_mul, mul_pow, mul_pow]
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgle 2)

/-- A fixed monic polynomial coprime to its derivative over the rationals
has subpolynomially many roots modulo every positive integer. The integer
Bezout certificate is explicit in this version. -/
theorem rootsMod_subpolynomial (f A B : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (C : ℕ) (hC : 0 < C)
    (hbez : A*f+B*f.derivative = Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ n : ℕ, 0 < n →
      ((rootsMod f n).card : ℝ) ≤ K*(n : ℝ)^ε := by
  have hdr : (0 : ℝ) < f.natDegree := by exact_mod_cast hd
  obtain ⟨K,hK,hdiv⟩ := divisor_count_subpolynomial (ε/f.natDegree) (div_pos hε hdr)
  refine ⟨K^f.natDegree*(C : ℝ)^2, by positivity, ?_⟩
  intro n hn
  have hb := rootsMod_divisor_bound f A B hf hd C hC hbez n
  have hg : Nat.gcd n C ≤ C := Nat.le_of_dvd hC (Nat.gcd_dvd_right _ _)
  have hbr : ((rootsMod f n).card : ℝ) ≤
      (n.divisors.card : ℝ)^f.natDegree*(C : ℝ)^2 := by
    exact_mod_cast hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg 2))
  calc
    ((rootsMod f n).card : ℝ) ≤ _ := hbr
    _ ≤ (K*(n : ℝ)^(ε/f.natDegree))^f.natDegree*(C : ℝ)^2 := by
      gcongr
      exact hdiv n hn
    _ = (K^f.natDegree*(C : ℝ)^2)*(n : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        div_mul_cancel₀ ε hdr.ne']
      ring

end Erdos322Research.PolynomialCongruenceRootBound
