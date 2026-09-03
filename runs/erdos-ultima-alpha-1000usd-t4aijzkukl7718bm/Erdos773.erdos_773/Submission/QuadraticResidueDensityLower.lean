import Submission.ElementarySquareSieve
import Submission.DivisorBound

/-!
A uniform lower bound for the proportion of square residues modulo an
arbitrary positive integer. This diagnoses a limitation of a modular
upper-bound method, not of Sidon subsets of squares themselves.
-/
namespace Erdos773.QuadraticResidueDensityLower
open Finset
noncomputable section
set_option maxHeartbeats 2000000

lemma linear_zero_card (q : ℕ) [NeZero q] (a : ℕ) :
    (univ.filter (fun x : ZMod q => (a : ZMod q)*x = 0)).card = q.gcd a := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod q) a
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, AddMonoidHom.mem_ker,
    nsmulAddMonoidHom_apply, nsmul_eq_mul, ZMod.card] using h

lemma linear_fiber_card (q : ℕ) [NeZero q] (a : ℕ) (b : ZMod q) :
    (univ.filter (fun x : ZMod q => (a : ZMod q)*x = b)).card ≤ q.gcd a := by
  classical
  by_cases he : (univ.filter (fun x : ZMod q => (a : ZMod q)*x = b)).Nonempty
  · obtain ⟨c, hc⟩ := he
    have hc' := (mem_filter.mp hc).2
    rw [← linear_zero_card q a]
    apply card_le_card_of_injOn (fun x : ZMod q => x-c)
    · intro x hx
      have hx' := (mem_filter.mp hx).2
      simp [mul_sub, hx', hc']
    · intro x _ y _ hxy
      exact sub_left_injective hxy
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp

lemma multiples_card (q d : ℕ) [NeZero q] (hd : d ∈ q.divisors) :
    (univ.filter (fun x : ZMod q => d ∣ x.val)).card ≤ q/d := by
  classical
  have hdq := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← card_range (q/d)]
  apply card_le_card_of_injOn (fun x : ZMod q => x.val/d)
  · intro x _
    change x.val/d ∈ range (q/d)
    rw [mem_range, Nat.div_lt_iff_lt_mul hd0, Nat.div_mul_cancel hdq]
    exact ZMod.val_lt x
  · intro x hx y hy hxy
    apply ZMod.val_injective q
    have hx' := Nat.div_mul_cancel (mem_filter.mp hx).2
    have hy' := Nat.div_mul_cancel (mem_filter.mp hy).2
    nlinarith

lemma sum_gcd_bound (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, q.gcd x.val) ≤ q * q.divisors.card := by
  classical
  have hn : q ≠ 0 := NeZero.ne q
  calc
    _ ≤ ∑ x : ZMod q, ∑ d ∈ q.divisors, if d ∣ x.val then d else 0 := by
      apply sum_le_sum
      intro x _
      have hd : q.gcd x.val ∈ q.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn⟩
      have hh := single_le_sum (s := q.divisors)
        (f := fun d => if d ∣ x.val then d else 0)
        (fun _ _ => Nat.zero_le _) hd
      simpa only [if_pos (Nat.gcd_dvd_right q x.val)] using hh
    _ = ∑ d ∈ q.divisors, ∑ x : ZMod q, if d ∣ x.val then d else 0 := sum_comm
    _ ≤ ∑ d ∈ q.divisors, q := by
      apply sum_le_sum
      intro d hd
      calc
        _ = (univ.filter (fun x : ZMod q => d ∣ x.val)).card*d := by
          rw [← sum_filter]
          simp
        _ ≤ (q/d)*d := Nat.mul_le_mul_right d (multiples_card q d hd)
        _ = q := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    _ = _ := by simp [mul_comm]

def zeroProducts (q : ℕ) [NeZero q] : Finset (ZMod q × ZMod q) :=
  univ.filter (fun p => p.1*p.2 = 0)

def squareEnergy (q : ℕ) [NeZero q] : Finset (ZMod q × ZMod q) :=
  univ.filter (fun p => p.1^2 = p.2^2)

lemma zero_products_bound (q : ℕ) [NeZero q] :
    (zeroProducts q).card ≤ q*q.divisors.card := by
  classical
  calc
    _ = ∑ x : ZMod q, ((zeroProducts q).filter (fun p => p.1=x)).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ x : ZMod q, q.gcd x.val := by
      apply sum_le_sum
      intro x _
      rw [← linear_zero_card q x.val]
      apply card_le_card_of_injOn Prod.snd
      · intro p hp
        obtain ⟨hp, hpx⟩ := mem_filter.mp hp
        have hz := (mem_filter.mp hp).2
        simp only [zeroProducts] at hp
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        rw [ZMod.natCast_zmod_val, ← hpx]
        exact hz
      · intro p hp r hr he
        exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hr).2.symm) he
    _ ≤ _ := sum_gcd_bound q

lemma square_energy_bound (q : ℕ) [NeZero q] :
    (squareEnergy q).card ≤ 2*q*q.divisors.card := by
  classical
  have hh : (squareEnergy q).card ≤ 2*(zeroProducts q).card := by
    apply card_le_mul_card_image_of_maps_to
      (f := fun p : ZMod q × ZMod q => (p.1-p.2,p.1+p.2))
    · intro p hp
      have hs := (mem_filter.mp hp).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      dsimp only
      calc
        _ = p.1^2-p.2^2 := by ring
        _ = 0 := sub_eq_zero.mpr hs
    · intro z _
      calc
        _ ≤ (univ.filter (fun x : ZMod q => (2 : ZMod q)*x=z.1+z.2)).card := by
          apply card_le_card_of_injOn Prod.fst
          · intro p hp
            have he := (mem_filter.mp hp).2
            have h1 := congrArg Prod.fst he
            have h2 := congrArg Prod.snd he
            dsimp only at h1 h2
            apply mem_filter.mpr
            refine ⟨mem_univ _, ?_⟩
            calc
              _ = (p.1-p.2)+(p.1+p.2) := by ring
              _ = z.1+z.2 := by rw [h1,h2]
          · intro p hp r hr he
            have h1 := congrArg Prod.fst (mem_filter.mp hp).2
            have h2 := congrArg Prod.fst (mem_filter.mp hr).2
            dsimp only at h1 h2
            apply Prod.ext he
            have hh : p.1-p.2=r.1-r.2 := h1.trans h2.symm
            rw [he] at hh
            exact sub_right_injective hh
        _ ≤ q.gcd 2 := linear_fiber_card q 2 _
        _ ≤ 2 := Nat.gcd_le_right q (by omega)
  exact hh.trans (by nlinarith [zero_products_bound q])

lemma energy_cauchy (q : ℕ) [NeZero q] :
    q^2 ≤ (quadraticResidues q).card * (squareEnergy q).card := by
  classical
  have hsum : q = ∑ r ∈ quadraticResidues q,
      (univ.filter (fun x : ZMod q => x^2=r)).card := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (ZMod q)))
      (t := quadraticResidues q) (f := fun x => x^2)
      (fun x _ => mem_image.mpr ⟨x,mem_univ _,rfl⟩)
    simpa only [card_univ, ZMod.card] using hh
  have hsum2 : (squareEnergy q).card = ∑ r ∈ quadraticResidues q,
      (univ.filter (fun x : ZMod q => x^2=r)).card^2 := by
    have hm : Set.MapsTo (fun p : ZMod q × ZMod q => p.1^2)
        (squareEnergy q : Set (ZMod q × ZMod q)) (quadraticResidues q) := by
      intro p _
      exact mem_image.mpr ⟨p.1,mem_univ _,rfl⟩
    rw [card_eq_sum_card_fiberwise hm]
    apply sum_congr rfl
    intro r _
    have he : (squareEnergy q).filter (fun p => p.1^2=r) =
        (univ.filter (fun x : ZMod q => x^2=r)) ×ˢ
          (univ.filter (fun x : ZMod q => x^2=r)) := by
      ext p
      simp only [squareEnergy, mem_filter, mem_univ, true_and, mem_product]
      aesop
    rw [he, card_product, pow_two]
  rw [hsum2]
  conv_lhs => rw [hsum]
  exact sq_sum_le_card_mul_sum_sq

/-- A uniform lower bound, valid for every positive modulus. -/
theorem residue_card_lower (q : ℕ) [NeZero q] :
    q ≤ 2*q.divisors.card*(quadraticResidues q).card := by
  have hc := energy_cauchy q
  have he := Nat.mul_le_mul_left (quadraticResidues q).card (square_energy_bound q)
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  nlinarith

theorem residue_density_lower (q : ℕ) [NeZero q] :
    1 ≤ 2*(q.divisors.card : ℝ)*quadraticResidueDensity q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hh : (q : ℝ) ≤ 2*q.divisors.card*(quadraticResidues q).card := by
    exact_mod_cast residue_card_lower q
  rw [quadraticResidueDensity_eq, ← mul_div_assoc]
  apply (le_div_iff₀ hq).mpr
  simpa only [one_mul] using hh

open Filter in
/-- Uniform subpower lower density; the constant is independent of q. -/
theorem density_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q →
      1 ≤ C*(q : ℝ)^δ*quadraticResidueDensity q := by
  obtain ⟨D, hD, hb⟩ := divisor_card_subpower δ hδ
  refine ⟨2*D, by positivity, ?_⟩
  intro q hq
  letI : NeZero q := ⟨hq.ne'⟩
  have hh := mul_le_mul_of_nonneg_right (hb q) (quadraticResidueDensity_nonneg q)
  have hl := residue_density_lower q
  nlinarith

open Filter in
/-- One eventual threshold works for every modulus up to N squared. -/
theorem density_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ N^2 →
      (N : ℝ)^(-ε) ≤ quadraticResidueDensity q := by
  obtain ⟨C, hC, hbound⟩ := density_subpower (ε/4) (by positivity)
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)^(ε/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop C)] with N hN hNC
  intro q hq hqN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hqNr : (q : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast hqN
  have hpow : (q : ℝ)^(ε/4) ≤ (N : ℝ)^(ε/2) := by
    calc
      _ ≤ ((N : ℝ)^2)^(ε/4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg q) hqNr (by positivity)
      _ = (N : ℝ)^(ε/2) := by
        rw [← Real.rpow_natCast_mul hNp.le]
        congr 1
        ring
  have hprod : C*(q : ℝ)^(ε/4) ≤ (N : ℝ)^ε := by
    calc
      _ ≤ (N : ℝ)^(ε/2)*(N : ℝ)^(ε/2) :=
        mul_le_mul hNC hpow (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by positivity)
      _ = (N : ℝ)^ε := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hprod (quadraticResidueDensity_nonneg q)
  have hone : 1 ≤ (N : ℝ)^ε*quadraticResidueDensity q := (hbound q hq).trans hh
  have hmul : (N : ℝ)^(-ε)*(N : ℝ)^ε = 1 := by
    rw [← Real.rpow_add hNp]
    simp
  have hm := mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg hNp.le (-ε))
  simpa only [mul_one, ← mul_assoc, hmul, one_mul] using hm

lemma small_squares_card (q N : ℕ) [NeZero q] (hN : N^2 ≤ q) :
    N ≤ (quadraticResidues q).card := by
  classical
  have hlt (n : ℕ) (hn : n ∈ range N) : n^2 < q :=
    (Nat.pow_lt_pow_left (mem_range.mp hn) (by omega : 2 ≠ 0)).trans_le hN
  rw [← card_range N]
  apply card_le_card_of_injOn (fun n : ℕ => (n : ZMod q)^2)
  · intro n _
    exact mem_image.mpr ⟨n,mem_univ _,rfl⟩
  · intro n hn m hm he
    have hh := congrArg ZMod.val he
    dsimp only at hh
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (hlt n hn), Nat.mod_eq_of_lt (hlt m hm)] at hh
    exact Nat.pow_left_injective (by omega : 2 ≠ 0) hh

lemma quotient_capacity (q N : ℕ) (hq : 0 < q) :
    (N : ℝ)^2 ≤ (q : ℝ)*(2*((N^2/q : ℕ) : ℝ)+1) := by
  have hh := Nat.lt_mul_div_succ (N^2) hq
  have hn : N^2 ≤ q*(2*(N^2/q)+1) :=
    hh.le.trans (Nat.mul_le_mul_left q (by omega))
  exact_mod_cast hn

open Filter in
/-- The exact residue-count inequality used for the upper bounds remains
consistent with the proposed real cardinality N^(1-epsilon), simultaneously
for ALL positive moduli. This is a limitation of those inequalities, not
a construction of a Sidon set and not a proof of Erdős 773. -/
theorem all_moduli_accept_subpower_card (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ) [NeZero q],
      ((N : ℝ)^(1-ε))^2 ≤ (quadraticResidues q).card *
        ((N : ℝ)^(1-ε) + 2*((N^2/q : ℕ) : ℝ) + 1) := by
  filter_upwards [density_uniform (2*ε) (by positivity), eventually_ge_atTop 1]
    with N hden hN
  intro q inst
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hM0 : 0 ≤ (N : ℝ)^(1-ε) := Real.rpow_nonneg hNp.le _
  have hM : (N : ℝ)^(1-ε) ≤ N := by
    calc
      _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  by_cases hqN : q ≤ N^2
  · have hd := hden q hq hqN
    have hsq : ((N : ℝ)^(1-ε))^2 = (N : ℝ)^(-(2*ε))*(N : ℝ)^2 := by
      rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_two (N : ℝ),
        ← Real.rpow_add hNp]
      congr 1
      ring
    have hprod : quadraticResidueDensity q*(q : ℝ) = (quadraticResidues q).card := by
      rw [quadraticResidueDensity_eq, div_mul_cancel₀ _ hqr.ne']
    calc
      _ = (N : ℝ)^(-(2*ε))*(N : ℝ)^2 := hsq
      _ ≤ quadraticResidueDensity q*(N : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      _ ≤ quadraticResidueDensity q*((q : ℝ)*(2*((N^2/q : ℕ) : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (quotient_capacity q N hq)
          (quadraticResidueDensity_nonneg q)
      _ = (quadraticResidues q).card*(2*((N^2/q : ℕ) : ℝ)+1) := by
        rw [← mul_assoc, hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  · have hr : (N : ℝ) ≤ (quadraticResidues q).card := by
      exact_mod_cast small_squares_card q N (by omega)
    have hmr := mul_le_mul_of_nonneg_right (hM.trans hr) hM0
    have hextra := mul_nonneg (Nat.cast_nonneg (α := ℝ) (quadraticResidues q).card)
      (show 0 ≤ 2*((N^2/q : ℕ) : ℝ)+1 by positivity)
    nlinarith

lemma downward_feasible {R K x y : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y^2 ≤ R*(y+K)) :
    x^2 ≤ R*(x+K) := by
  by_cases hxR : x ≤ R
  · have h1 := mul_le_mul_of_nonneg_right hxR hx
    have h2 := mul_nonneg hR hK
    nlinarith
  · have h1 : 0 ≤ x+y-R := by linarith
    have h2 := mul_nonneg (sub_nonneg.mpr hxy) h1
    nlinarith

open Filter in
/-- Even a single INTEGER cardinality of conjectured size can satisfy all
of the exact modular inequalities simultaneously. No Sidon set realizing
this integer is asserted. -/
theorem integer_cardinality_model (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ m : ℕ, m ≤ N ∧ (N : ℝ)^(1-ε) ≤ m ∧
      ∀ (q : ℕ) [NeZero q],
        m^2 ≤ (quadraticResidues q).card*(m+2*(N^2/q)+1) := by
  let η : ℝ := min ε (1/2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ 1/2 := min_le_right _ _
  have hlim : Tendsto (fun N : ℕ => (N : ℝ)^(η/2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < η/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [all_moduli_accept_subpower_card (η/2) (by positivity),
    eventually_ge_atTop 1, hlim.eventually (eventually_ge_atTop (2 : ℝ))]
    with N hmod hN hpow
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hx0 : 0 ≤ (N : ℝ)^(1-η) := Real.rpow_nonneg hNp.le _
  have hx1 : 1 ≤ (N : ℝ)^(1-η) := Real.one_le_rpow hNr (by linarith)
  have hxN : (N : ℝ)^(1-η) ≤ N := by
    calc
      _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      _ = N := Real.rpow_one _
  let m : ℕ := ⌈(N : ℝ)^(1-η)⌉₊
  have hmN : m ≤ N := Nat.ceil_le.mpr hxN
  have hxm : (N : ℝ)^(1-η) ≤ m := Nat.le_ceil _
  have hmupper : (m : ℝ) ≤ (N : ℝ)^(1-η/2) := by
    have hceil : (m : ℝ) < (N : ℝ)^(1-η)+1 := Nat.ceil_lt_add_one hx0
    have hh := mul_le_mul_of_nonneg_left hpow hx0
    have he : (N : ℝ)^(1-η)*(N : ℝ)^(η/2) = (N : ℝ)^(1-η/2) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    rw [he] at hh
    linarith
  refine ⟨m, hmN, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hNr (by linarith : 1-ε ≤ 1-η)).trans hxm
  · intro q inst
    have hh := downward_feasible
      (R := ((quadraticResidues q).card : ℝ))
      (K := 2*((N^2/q : ℕ) : ℝ)+1)
      (Nat.cast_nonneg _) (by positivity) (Nat.cast_nonneg m) hmupper
      (by simpa only [add_assoc] using hmod q)
    simp only [← add_assoc] at hh
    exact_mod_cast hh

#print axioms linear_zero_card
#print axioms linear_fiber_card
#print axioms sum_gcd_bound
#print axioms square_energy_bound
#print axioms residue_card_lower
#print axioms residue_density_lower
#print axioms density_subpower
#print axioms density_uniform
#print axioms small_squares_card
#print axioms all_moduli_accept_subpower_card
#print axioms integer_cardinality_model
end
end Erdos773.QuadraticResidueDensityLower
