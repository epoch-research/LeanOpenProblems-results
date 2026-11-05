import Submission.Basic

/-!
# The global CRT construction for distinct subset sums

This file proves the global counterfamily conditional on the shared `BlockSupply`
interface.  It neither imports the problem statement nor assumes a block supply.
-/

namespace ErdosDSS

open scoped BigOperators

namespace CRT

/-- Concatenation after scaling the two rows by the opposite periods. -/
def append {n m : ℕ} (P p : ℕ) (W : Fin n → ℕ) (a : Fin m → ℕ) :
    Fin (n + m) → ℕ :=
  Fin.addCases (fun i => p * W i) (fun i => P * a i)

lemma signedSum_append {n m : ℕ} (P p : ℕ) (W : Fin n → ℕ) (a : Fin m → ℕ)
    (e : Fin (n + m) → ℤ) :
    signedSum (append P p W a) e =
      (p : ℤ) * signedSum W (fun i => e (Fin.castAdd m i)) +
      (P : ℤ) * signedSum a (fun i => e (Fin.natAdd n i)) := by
  unfold signedSum
  rw [Fin.sum_univ_add]
  simp only [append, Fin.addCases_left, Fin.addCases_right, Nat.cast_mul,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- Any return of a ternary row whose entries are bounded by its positive
period has height between minus and plus the number of entries. -/
lemma return_height_bound {n P : ℕ} (W : Fin n → ℕ) (hP : 0 < P)
    (hW : ∀ i, W i ≤ P) (e : Fin n → ℤ) (he : Ternary e) (k : ℤ)
    (hk : signedSum W e = k * (P : ℤ)) :
    -(n : ℤ) ≤ k ∧ k ≤ (n : ℤ) := by
  have hPz : 0 < (P : ℤ) := by exact_mod_cast hP
  have hupper : signedSum W e ≤ (n : ℤ) * (P : ℤ) := by
    calc
      signedSum W e ≤ ∑ _i : Fin n, (P : ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hWi : 0 ≤ (W i : ℤ) := by positivity
        have hWiP : (W i : ℤ) ≤ (P : ℤ) := by exact_mod_cast hW i
        have hei := he i
        nlinarith
      _ = (n : ℤ) * (P : ℤ) := by simp
  have hlower : -(n : ℤ) * (P : ℤ) ≤ signedSum W e := by
    calc
      -(n : ℤ) * (P : ℤ) = ∑ _i : Fin n, -(P : ℤ) := by simp
      _ ≤ signedSum W e := by
        apply Finset.sum_le_sum
        intro i hi
        have hWi : 0 ≤ (W i : ℤ) := by positivity
        have hWiP : (W i : ℤ) ≤ (P : ℤ) := by exact_mod_cast hW i
        have hei := he i
        nlinarith
  rw [hk] at hupper hlower
  exact ⟨(mul_le_mul_iff_left₀ hPz).mp hlower,
    (mul_le_mul_iff_left₀ hPz).mp hupper⟩

/-- A congruence to one makes the old and new periods coprime. -/
lemma block_coprime {q P : ℕ} (b : ReturnBlock q P) : Nat.Coprime P b.p := by
  have h : Nat.Coprime b.p P := by
    unfold Nat.Coprime
    simpa using b.residue.gcd_eq
  exact h.symm

/-- The CRT step preserves rigidity of the zero signed sum.  Nonzero new
returns cannot cancel an old return because the new height exceeds `n`. -/
lemma append_zero_rigid {n P q : ℕ} (W : Fin n → ℕ) (hP : 0 < P)
    (hW : ∀ i, W i ≤ P)
    (hzero : ∀ e : Fin n → ℤ, Ternary e → signedSum W e = 0 → e = 0)
    (b : ReturnBlock q P) (hq : n < q) :
    ∀ e : Fin (n + b.n) → ℤ, Ternary e →
      signedSum (append P b.p W b.a) e = 0 → e = 0 := by
  intro e he hsum
  let eL : Fin n → ℤ := fun i => e (Fin.castAdd b.n i)
  let eR : Fin b.n → ℤ := fun i => e (Fin.natAdd n i)
  have heL : Ternary eL := fun i => he _
  have heR : Ternary eR := fun i => he _
  have hsplit : (b.p : ℤ) * signedSum W eL +
      (P : ℤ) * signedSum b.a eR = 0 := by
    simpa only [signedSum_append, eL, eR] using hsum
  have hcop : Int.gcd (P : ℤ) (b.p : ℤ) = 1 := by
    simpa only [Int.gcd_natCast_natCast] using block_coprime b
  have hdiv : (P : ℤ) ∣ (b.p : ℤ) * signedSum W eL := by
    refine ⟨-signedSum b.a eR, ?_⟩
    linear_combination hsplit
  obtain ⟨k, hk⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hdiv hcop
  have hk' : signedSum W eL = k * (P : ℤ) := by
    simpa only [mul_comm] using hk
  have hbound := return_height_bound W hP hW eL heL k hk'
  have hPz : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  have hreturn : signedSum b.a eR = (-k) * (b.p : ℤ) := by
    have hfactor : (P : ℤ) * ((b.p : ℤ) * k + signedSum b.a eR) = 0 := by
      calc
        _ = (b.p : ℤ) * signedSum W eL + (P : ℤ) * signedSum b.a eR := by
          rw [hk']
          ring
        _ = 0 := hsplit
    have hinner := (mul_eq_zero.mp hfactor).resolve_left hPz
    linear_combination hinner
  have hqz : (n : ℤ) < (q : ℤ) := by exact_mod_cast hq
  rcases b.returns eR heR (-k) hreturn with ⟨hR, hk0⟩ | hqplus | hqminus
  · have hk0' : k = 0 := by omega
    have hL : eL = 0 := hzero eL heL (by rw [hk', hk0']; simp)
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact congrFun hL j
    · intro j
      exact congrFun hR j
  · omega
  · omega

/-- An efficient positive row with no nontrivial zero ternary signed sum. -/
structure GlobalRow (J : ℕ) where
  n : ℕ
  P : ℕ
  W : Fin n → ℕ
  P_pos : 0 < P
  P_odd : Odd P
  small : ∀ i, 0 < W i ∧ W i < P
  zero_rigid : ∀ e : Fin n → ℤ, Ternary e → signedSum W e = 0 → e = 0
  efficiency : 4 ^ J * P ≤ 3 ^ J * 2 ^ n
  period_large : 0 < J → 1 < P

/-- The empty row has period one, including the modulus-one base case. -/
def GlobalRow.empty : GlobalRow 0 where
  n := 0
  P := 1
  W := Fin.elim0
  P_pos := by decide
  P_odd := by decide
  small := fun i => Fin.elim0 i
  zero_rigid := fun e _ _ => Subsingleton.elim e 0
  efficiency := by norm_num
  period_large := by omega

lemma block_n_pos {q P : ℕ} (b : ReturnBlock q P) : 0 < b.n := by
  by_contra hn
  have hn0 : b.n = 0 := by omega
  have heff := b.efficiency
  simp only [hn0, pow_zero, mul_one] at heff
  have hp := b.p_pos
  omega

lemma block_period_two_le {q P : ℕ} (b : ReturnBlock q P) : 2 ≤ b.p := by
  have hn := block_n_pos b
  have hi := b.small ⟨0, hn⟩
  omega

/-- One CRT extension multiplies the period and gains one factor `3/4`
in the period-to-power-of-two ratio. -/
def GlobalRow.extend {J q : ℕ} (r : GlobalRow J) (b : ReturnBlock q r.P)
    (hq : r.n < q) : GlobalRow (J + 1) where
  n := r.n + b.n
  P := r.P * b.p
  W := append r.P b.p r.W b.a
  P_pos := Nat.mul_pos r.P_pos b.p_pos
  P_odd := r.P_odd.mul b.p_odd
  small := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [append, Fin.addCases_left]
      exact ⟨Nat.mul_pos b.p_pos (r.small j).1,
        by simpa only [mul_comm] using
          Nat.mul_lt_mul_of_pos_left (r.small j).2 b.p_pos⟩
    · intro j
      simp only [append, Fin.addCases_right]
      exact ⟨Nat.mul_pos r.P_pos (b.small j).1,
        Nat.mul_lt_mul_of_pos_left (b.small j).2 r.P_pos⟩
  zero_rigid := append_zero_rigid r.W r.P_pos
    (fun i => (r.small i).2.le) r.zero_rigid b hq
  efficiency := by
    calc
      4 ^ (J + 1) * (r.P * b.p) = (4 ^ J * r.P) * (4 * b.p) := by
        rw [pow_succ]
        ring
      _ ≤ (3 ^ J * 2 ^ r.n) * (3 * 2 ^ b.n) :=
        Nat.mul_le_mul r.efficiency b.efficiency
      _ = 3 ^ (J + 1) * 2 ^ (r.n + b.n) := by
        rw [pow_succ, pow_add]
        ring
  period_large := by
    intro hJ
    have hp := block_period_two_le b
    have hP := r.P_pos
    nlinarith

/-- Repeatedly request a block with return height greater than the current
row length.  The only input is the explicit supply hypothesis. -/
theorem exists_globalRow (hs : BlockSupply) (J : ℕ) : Nonempty (GlobalRow J) := by
  induction J with
  | zero => exact ⟨GlobalRow.empty⟩
  | succ J ih =>
      obtain ⟨r⟩ := ih
      obtain ⟨q, hq, ⟨b⟩⟩ := hs r.P r.P_pos r.P_odd r.n
      exact ⟨r.extend b hq⟩

/-- Zero ternary rigidity distinguishes the sums of arbitrary subsets of
an indexed row. -/
lemma indexed_subset_sum_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → ℕ)
    (hzero : ∀ e : ι → ℤ, Ternary e → signedSum W e = 0 → e = 0) :
    Function.Injective (fun S : Finset ι => S.sum W) := by
  intro S T hST
  let e : ι → ℤ := fun i =>
    (if i ∈ S then 1 else 0) - (if i ∈ T then 1 else 0)
  have he : Ternary e := by
    intro i
    dsimp [e]
    split_ifs <;> norm_num
  have hsum : signedSum W e = 0 := by
    have hSTz : (∑ i ∈ S, (W i : ℤ)) = ∑ i ∈ T, (W i : ℤ) := by
      exact_mod_cast hST
    simp only [signedSum, e, sub_mul, Finset.sum_sub_distrib, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_mem_eq]
    exact sub_eq_zero.mpr hSTz
  have he0 := hzero e he hsum
  ext i
  have hi : e i = 0 := congrFun he0 i
  dsimp [e] at hi
  constructor
  · intro hiS
    by_contra hiT
    simp [hiS, hiT] at hi
  · intro hiT
    by_contra hiS
    simp [hiS, hiT] at hi

/-- In particular, a zero-rigid row has no repeated entries. -/
lemma indexed_row_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → ℕ)
    (hzero : ∀ e : ι → ℤ, Ternary e → signedSum W e = 0 → e = 0) :
    Function.Injective W := by
  intro i j hij
  have hsets : ({i} : Finset ι) = {j} :=
    indexed_subset_sum_injective W hzero (by simpa only [Finset.sum_singleton] using hij)
  exact Finset.singleton_inj.mp hsets

/-- Every subset of the image is the image of its indexed inverse image. -/
lemma image_filter_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.univ.image W) :
    (Finset.univ.filter (fun i => W i ∈ S)).image W = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    have hiS := (Finset.mem_filter.mp hi).2
    exact hix ▸ hiS
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hS hx)
    refine Finset.mem_image.mpr ⟨i, ?_, hix⟩
    apply Finset.mem_filter.mpr
    exact ⟨hi, hix.symm ▸ hx⟩

/-- The image of a zero-rigid indexed row has distinct subset sums in the
literal finite-set formulation of the problem. -/
lemma image_subset_sum_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → ℕ)
    (hzero : ∀ e : ι → ℤ, Ternary e → signedSum W e = 0 → e = 0) :
    (fun (⟨S, _⟩ : (Finset.univ.image W).powerset) => S.sum id).Injective := by
  intro ⟨S, hS⟩ ⟨T, hT⟩ hST
  have hWinj := indexed_row_injective W hzero
  let s : Finset ι := Finset.univ.filter (fun i => W i ∈ S)
  let t : Finset ι := Finset.univ.filter (fun i => W i ∈ T)
  have hs : s.image W = S := image_filter_eq W S (Finset.mem_powerset.mp hS)
  have ht : t.image W = T := image_filter_eq W T (Finset.mem_powerset.mp hT)
  have hsumS : S.sum id = s.sum W := by
    rw [← hs, Finset.sum_image (fun i _ j _ hij => hWinj hij)]
    rfl
  have hsumT : T.sum id = t.sum W := by
    rw [← ht, Finset.sum_image (fun i _ j _ hij => hWinj hij)]
    rfl
  have hst : s.sum W = t.sum W := by
    calc
      _ = S.sum id := hsumS.symm
      _ = T.sum id := hST
      _ = _ := hsumT
  have hst' : s = t := indexed_subset_sum_injective W hzero hst
  apply Subtype.ext
  calc
    S = s.image W := hs.symm
    _ = t.image W := congrArg (Finset.image W) hst'
    _ = T := ht

end CRT

/-- A block supply gives a finite family beating every prescribed power
of `3/4`.  The bound is strict because the entries lie below the period,
so the enclosing interval can end at `P - 1`. -/
theorem blockSupply_counterFamily (hs : BlockSupply) :
    ∀ J : ℕ, 0 < J → ∃ (N : ℕ) (A : Finset ℕ),
      (A ⊆ Finset.Icc 1 N ∧
        (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) ∧
      N ≠ 0 ∧ 4 ^ J * N < 3 ^ J * 2 ^ A.card := by
  intro J hJ
  obtain ⟨r⟩ := CRT.exists_globalRow hs J
  let A : Finset ℕ := Finset.univ.image r.W
  let N : ℕ := r.P - 1
  have hcard : A.card = r.n := by
    dsimp [A]
    rw [Finset.card_image_of_injective _ (CRT.indexed_row_injective r.W r.zero_rigid)]
    exact Finset.card_fin _
  have hP : 1 < r.P := r.period_large hJ
  refine ⟨N, A, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_Icc.mpr
    have hsmall := r.small i
    dsimp [N]
    omega
  · exact CRT.image_subset_sum_injective r.W r.zero_rigid
  · dsimp [N]
    omega
  · have h4pos : 0 < 4 ^ J := by positivity
    calc
      4 ^ J * N < 4 ^ J * r.P :=
        Nat.mul_lt_mul_of_pos_left (by dsimp [N]; omega) h4pos
      _ ≤ 3 ^ J * 2 ^ r.n := r.efficiency
      _ = 3 ^ J * 2 ^ A.card := by rw [hcard]

/-- A conditional negation of exactly the real-constant statement in the
problem.  No problem file is imported, and the sole construction hypothesis
is the shared block-supply interface. -/
theorem blockSupply_not_erdosStatement (hs : BlockSupply) :
    ¬ (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
      (A ⊆ Finset.Icc 1 N ∧
        (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) →
      N ≠ 0 → C * 2 ^ A.card < (N : ℝ)) := by
  rintro ⟨C, hCpos, hC⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (3 / 4 : ℝ) ^ K < C :=
    exists_pow_lt_of_lt_one hCpos (by norm_num)
  let J : ℕ := K + 1
  have hJ : 0 < J := by omega
  have hsmall : (3 / 4 : ℝ) ^ J < C := by
    dsimp [J]
    rw [pow_succ]
    have hnonneg : 0 ≤ (3 / 4 : ℝ) ^ K := pow_nonneg (by norm_num) _
    nlinarith
  obtain ⟨N, A, hDSS, hN, hbound⟩ := blockSupply_counterFamily hs J hJ
  have hcast : (4 : ℝ) ^ J * (N : ℝ) < (3 : ℝ) ^ J * (2 : ℝ) ^ A.card := by
    exact_mod_cast hbound
  have h4 : 0 < (4 : ℝ) ^ J := pow_pos (by norm_num) _
  have hratio : (N : ℝ) < (3 / 4 : ℝ) ^ J * (2 : ℝ) ^ A.card := by
    calc
      (N : ℝ) < ((3 : ℝ) ^ J * (2 : ℝ) ^ A.card) / (4 : ℝ) ^ J := by
        apply (lt_div_iff₀ h4).2
        simpa only [mul_comm] using hcast
      _ = (3 / 4 : ℝ) ^ J * (2 : ℝ) ^ A.card := by
        rw [div_pow]
        ring
  have h2 : 0 < (2 : ℝ) ^ A.card := pow_pos (by norm_num) _
  have hupper : (N : ℝ) < C * (2 : ℝ) ^ A.card :=
    lt_trans hratio (mul_lt_mul_of_pos_right hsmall h2)
  exact (lt_asymm hupper) (hC N A hDSS hN)

end ErdosDSS
