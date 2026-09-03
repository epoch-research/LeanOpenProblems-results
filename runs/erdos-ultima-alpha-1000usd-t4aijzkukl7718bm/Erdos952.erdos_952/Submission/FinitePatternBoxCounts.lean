import Submission.FinitePatternCRTCounts

/-! Elementary finite-box bounds from exact periodic counts. The size of the
period is retained in the bound; this file does not supply the growing-length
estimate required to exclude a Gaussian prime ray. -/
namespace Erdos952Investigation.FinitePatternBoxCounts
open AdmissibleRay FinitePatternAdmissibility FinitePatternLocalCounts FinitePatternCRTCounts
set_option maxHeartbeats 0

def indexEncoding (M R : ℕ) (i : Fin R) : ZMod M × Fin (R/M+1) :=
  ((i.val : ZMod M),⟨i.val/M,Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)⟩)

lemma indexEncoding_injective (M R : ℕ) : Function.Injective (indexEncoding M R) := by
  intro i j he
  have hr := congrArg Prod.fst he
  have hq := congrArg (fun a : ZMod M × Fin (R/M+1) => a.2.val) he
  change i.val/M = j.val/M at hq
  change (i.val : ZMod M) = (j.val : ZMod M) at hr
  have hm := (ZMod.natCast_eq_natCast_iff' i.val j.val M).mp hr
  have hi := Nat.mod_add_div i.val M
  have hj := Nat.mod_add_div j.val M
  rw [hq,hm] at hi
  exact Fin.ext (by omega)

def boxPoint {R : ℕ} (t : GaussianInt) (i : Fin R × Fin R) : GaussianInt :=
  t+⟨i.1.val,i.2.val⟩

def boxResidue {R : ℕ} (M : ℕ) (t : GaussianInt) (i : Fin R × Fin R) :
    ZMod M × ZMod M := ((boxPoint t i).re,(boxPoint t i).im)

def boxEncoding (M R : ℕ) (t : GaussianInt) (i : Fin R × Fin R) :
    (ZMod M × ZMod M) × (Fin (R/M+1) × Fin (R/M+1)) :=
  (boxResidue M t i,((indexEncoding M R i.1).2,(indexEncoding M R i.2).2))

lemma boxEncoding_injective (M R : ℕ) (t : GaussianInt) :
    Function.Injective (boxEncoding M R t) := by
  intro i j he
  have hr := congrArg (fun a : (ZMod M × ZMod M) ×
    (Fin (R/M+1) × Fin (R/M+1)) => a.1.1) he
  have hi := congrArg (fun a : (ZMod M × ZMod M) ×
    (Fin (R/M+1) × Fin (R/M+1)) => a.1.2) he
  simp only [boxEncoding,boxResidue,boxPoint,Zsqrtd.re_add,Zsqrtd.im_add,
    Int.cast_add,Int.cast_natCast] at hr hi
  have hqr := congrArg (fun a : (ZMod M × ZMod M) ×
    (Fin (R/M+1) × Fin (R/M+1)) => a.2.1) he
  have hqi := congrArg (fun a : (ZMod M × ZMod M) ×
    (Fin (R/M+1) × Fin (R/M+1)) => a.2.2) he
  apply Prod.ext
  · apply indexEncoding_injective M R
    exact Prod.ext (add_left_cancel hr) hqr
  · apply indexEncoding_injective M R
    exact Prod.ext (add_left_cancel hi) hqi

/-- A periodic subset has at most (floor(R/M)+1)^2 representatives of each
allowed residue pair in an R-by-R square, regardless of the square's anchor. -/
theorem periodic_box_count_le (M R : ℕ) (hM : 0 < M) (t : GaussianInt)
    (P : ZMod M × ZMod M → Prop) :
    Nat.card {i : Fin R × Fin R // P (boxResidue M t i)} ≤
      Nat.card {ab : ZMod M × ZMod M // P ab}*(R/M+1)^2 := by
  letI : NeZero M := ⟨hM.ne'⟩
  let f : {i : Fin R × Fin R // P (boxResidue M t i)} →
      {ab : ZMod M × ZMod M // P ab} × (Fin (R/M+1) × Fin (R/M+1)) :=
    fun i => (⟨boxResidue M t i.val,i.property⟩,(boxEncoding M R t i.val).2)
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply boxEncoding_injective M R t
    have hh := congrArg (fun a : {ab : ZMod M × ZMod M // P ab} ×
      (Fin (R/M+1) × Fin (R/M+1)) => (a.1.val,a.2)) he
    exact hh
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod,Nat.card_fin,pow_two] using hh

noncomputable def sieveBoxCount {ι τ : Type*} [Fintype τ]
    (z : ι → GaussianInt) (q : τ → ℕ) (t : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {i : Fin R × Fin R // ∀ j k, ¬ (q j : ℤ) ∣ (boxPoint t i+z k).norm}

/-- The product formula produces a finite-box upper bound, with the entire
modulus-dependent loss displayed explicitly. -/
theorem sieveBoxCount_le {ι τ : Type*} [Fintype τ]
    (z : ι → GaussianInt) (q : τ → ℕ) (hM : 0 < modulus q)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (t : GaussianInt) (R : ℕ) :
    sieveBoxCount z q t R ≤ (∏ j, localCount z (q j))*(R/modulus q+1)^2 := by
  have he : sieveBoxCount z q t R =
      Nat.card {i : Fin R × Fin R // GoodResidue z q (boxResidue (modulus q) t i)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    exact (goodResidue_integer_iff z q (boxPoint t i)).symm
  rw [he,← periodicCount_eq_product z q hc]
  exact periodic_box_count_le (modulus q) R hM t (GoodResidue z q)

/-- Every sufficiently large prime translate is counted by the sieve. The
threshold is imposed separately at every vertex, so no small-prime exception
is silently removed. -/
lemma large_prime_translate_sieved {ι τ : Type*}
    (z : ι → GaussianInt) (q : τ → ℕ) (hq : ∀ j, (q j).Prime)
    (t : GaussianInt) (hp : ∀ i, Prime (t+z i))
    (hl : ∀ j i, (q j : ℤ)^2 < (t+z i).norm) :
    ∀ j i, ¬ (q j : ℤ) ∣ (t+z i).norm := by
  intro j i hd
  have hh := prime_norm_divisor_bound (hp i) (hq j) hd
  exact (hl j i).not_ge hh

/-- The box bound applies to actual prime configurations after explicitly
excluding the finite small-norm exceptions. -/
theorem large_prime_box_count_le {ι τ : Type*} [Fintype τ]
    (z : ι → GaussianInt) (q : τ → ℕ) (hq : ∀ j, (q j).Prime)
    (hc : Pairwise (fun i j => (q i).Coprime (q j))) (t : GaussianInt) (R : ℕ) :
    Nat.card {b : Fin R × Fin R // (∀ i, Prime (boxPoint t b+z i)) ∧
      (∀ j i, (q j : ℤ)^2 < (boxPoint t b+z i).norm)} ≤
      (∏ j, localCount z (q j))*(R/modulus q+1)^2 := by
  have hM : 0 < modulus q := by
    apply Finset.prod_pos
    intro j _
    exact (hq j).pos
  apply le_trans _ (sieveBoxCount_le z q hM hc t R)
  let f : {b : Fin R × Fin R // (∀ i, Prime (boxPoint t b+z i)) ∧
      (∀ j i, (q j : ℤ)^2 < (boxPoint t b+z i).norm)} →
      {b : Fin R × Fin R // ∀ j i, ¬ (q j : ℤ) ∣ (boxPoint t b+z i).norm} :=
    fun b => ⟨b.val,large_prime_translate_sieved z q hq (boxPoint t b.val)
      b.property.1 b.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro b c h
  apply Subtype.ext
  exact congrArg (fun a : {b : Fin R × Fin R //
    ∀ j i, ¬ (q j : ℤ) ∣ (boxPoint t b+z i).norm} => a.val) h


lemma sub_square_ge (p k : ℕ) (h : 2*k+2 ≤ p) : p ≤ (p-k)^2 := by
  have hk : k ≤ p := by omega
  have he := Nat.sub_add_cancel hk
  have hd : 2 ≤ p-k := by omega
  nlinarith

lemma linear_le_periodic_bound (M R A : ℕ) (hM : 0 < M) (hA : M ≤ A) :
    R ≤ A*(R/M+1)^2 := by
  have hm := Nat.mod_lt R hM
  have he := Nat.mod_add_div R M
  have hR : R ≤ M*(R/M+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hsq : R/M+1 ≤ (R/M+1)^2 := by nlinarith
  exact hR.trans ((Nat.mul_le_mul_right _ hA).trans (Nat.mul_le_mul_left A hsq))

/-- For primes at least 2k+2, the product of the local counts is already at
least the modulus, irrespective of projection collisions. -/
theorem large_split_prime_product_ge_modulus {ι τ : Type*} [Fintype ι] [Fintype τ]
    (z : ι → GaussianInt) (q : τ → ℕ) (hq : ∀ j, (q j).Prime)
    (h2 : ∀ j, q j ≠ 2) (r : ∀ j, ZMod (q j)) (hr : ∀ j, (r j)^2 = -1)
    (hl : ∀ j, 2*Fintype.card ι+2 ≤ q j) :
    modulus q ≤ ∏ j, localCount z (q j) := by
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro j _
  exact (sub_square_ge (q j) (Fintype.card ι) (hl j)).trans
    (split_local_count_lower z (hq j) (h2 j) (r j) (hr j))

/-- Limitation of the elementary CRT box bound: using only these large split
primes cannot make its right side smaller than the side length R. This is a
lower bound on an UPPER-BOUND EXPRESSION, not a lower bound on actual primes
or on the actual number of surviving translates in a particular box. -/
theorem large_split_prime_box_bound_not_sublinear {ι τ : Type*}
    [Fintype ι] [Fintype τ] (z : ι → GaussianInt) (q : τ → ℕ)
    (hq : ∀ j, (q j).Prime) (h2 : ∀ j, q j ≠ 2)
    (r : ∀ j, ZMod (q j)) (hr : ∀ j, (r j)^2 = -1)
    (hl : ∀ j, 2*Fintype.card ι+2 ≤ q j) (R : ℕ) :
    R ≤ (∏ j, localCount z (q j))*(R/modulus q+1)^2 := by
  have hM : 0 < modulus q := by
    apply Finset.prod_pos
    intro j _
    exact (hq j).pos
  exact linear_le_periodic_bound (modulus q) R _ hM
    (large_split_prime_product_ge_modulus z q hq h2 r hr hl)

#print axioms large_split_prime_box_bound_not_sublinear

#print axioms periodic_box_count_le
#print axioms sieveBoxCount_le
#print axioms large_prime_box_count_le
end Erdos952Investigation.FinitePatternBoxCounts
