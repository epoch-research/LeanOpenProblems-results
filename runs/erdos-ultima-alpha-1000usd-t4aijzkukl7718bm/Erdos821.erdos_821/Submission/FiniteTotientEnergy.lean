import Submission.PrimitiveTotientCollisions

/-!
# Exact finite-support collision energy

Adding an input prime gives an exact nonnegative cross-correlation term.
This file does not assert that the cross-correlations force divergence for
all exponents below one, which would be needed to settle Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.FiniteEnergy

noncomputable def output (S : Finset ℕ) : ℕ := ∏ p ∈ S, (p-1)

lemma output_eq_totient (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    output S = Nat.totient (∏ p ∈ S, p) :=
  (totient_prod_primes S hS).symm

lemma output_insert (S : Finset ℕ) (p : ℕ) (hp : p ∉ S) :
    output (insert p S) = (p-1)*output S := by
  exact Finset.prod_insert hp

noncomputable def kernel (s : ℝ) (a b : ℕ) : ℝ :=
  if a = b then (a : ℝ)^(-(2*s)) else 0

lemma kernel_nonneg (s : ℝ) (a b : ℕ) : 0 ≤ kernel s a b := by
  unfold kernel
  split_ifs <;> positivity

lemma kernel_symm (s : ℝ) (a b : ℕ) : kernel s a b = kernel s b a := by
  unfold kernel
  by_cases h : a = b
  · subst b; rfl
  · simp [h, Ne.symm h]

lemma kernel_mul (s : ℝ) (d a b : ℕ) (hd : 0 < d) :
    kernel s (d*a) (d*b) = (d : ℝ)^(-(2*s))*kernel s a b := by
  unfold kernel
  by_cases h : a = b
  · subst b
    simp only [ite_true, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hm : d*a ≠ d*b := fun he => h (Nat.eq_of_mul_eq_mul_left hd he)
    simp only [hm, h, ite_false, mul_zero]

lemma kernel_shift (s : ℝ) (d a b : ℕ) :
    kernel s a (d*b) = (d : ℝ)^(-(2*s)) *
      (if a = d*b then (b : ℝ)^(-(2*s)) else 0) := by
  unfold kernel
  by_cases h : a = d*b
  · subst a
    simp only [ite_true, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [h, ite_false, mul_zero]

noncomputable def energy (P : Finset ℕ) (s : ℝ) : ℝ :=
  ∑ S ∈ P.powerset, ∑ T ∈ P.powerset, kernel s (output S) (output T)

noncomputable def correlation (P : Finset ℕ) (d : ℕ) (s : ℝ) : ℝ :=
  ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
    if output S = d*output T then (output T : ℝ)^(-(2*s)) else 0

lemma energy_nonneg (P : Finset ℕ) (s : ℝ) : 0 ≤ energy P s := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => kernel_nonneg _ _ _))

lemma correlation_nonneg (P : Finset ℕ) (d : ℕ) (s : ℝ) :
    0 ≤ correlation P d s := by
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.sum_nonneg
  intro T hT
  split_ifs <;> positivity

lemma energy_empty (s : ℝ) : energy ∅ s = 1 := by
  simp [energy, kernel, output]

/-- This identity holds for any finite set of integers; primality is only
needed when identifying outputs with totients of squarefree inputs. -/
theorem energy_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) (hp1 : 1 < p) (s : ℝ) :
    energy (insert p P) s =
      (1 + ((p-1 : ℕ) : ℝ)^(-(2*s)))*energy P s +
        2*((p-1 : ℕ) : ℝ)^(-(2*s))*correlation P (p-1) s := by
  have hn (S : Finset ℕ) (hS : S ∈ P.powerset) : p ∉ S :=
    fun h => hp ((Finset.mem_powerset.mp hS) h)
  have hsplit (S : Finset ℕ) :
      (∑ T ∈ (insert p P).powerset, kernel s (output S) (output T)) =
        (∑ T ∈ P.powerset, kernel s (output S) (output T)) +
          ∑ T ∈ P.powerset, kernel s (output S) ((p-1)*output T) := by
    rw [Finset.sum_powerset_insert hp]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [output_insert _ _ (hn T hT)]
  have hscale : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      kernel s ((p-1)*output S) ((p-1)*output T)) =
      ((p-1 : ℕ) : ℝ)^(-(2*s))*energy P s := by
    simp only [kernel_mul _ _ _ _ (Nat.sub_pos_of_lt hp1)]
    simp only [energy, Finset.mul_sum]
  have hcross : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      kernel s (output S) ((p-1)*output T)) =
      ((p-1 : ℕ) : ℝ)^(-(2*s))*correlation P (p-1) s := by
    simp only [kernel_shift, correlation, Finset.mul_sum]
  have hcross' : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      kernel s ((p-1)*output S) (output T)) =
      ((p-1 : ℕ) : ℝ)^(-(2*s))*correlation P (p-1) s := by
    rw [Finset.sum_comm]
    simp only [kernel_symm s ((p-1)*_)]
    exact hcross
  unfold energy
  rw [Finset.sum_powerset_insert hp]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have he1 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      kernel s (output (insert p S)) (output T)) =
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        kernel s ((p-1)*output S) (output T) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [output_insert _ _ (hn S hS)]
  have he2 : (∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
      kernel s (output (insert p S)) ((p-1)*output T)) =
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset,
        kernel s ((p-1)*output S) ((p-1)*output T) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [output_insert _ _ (hn S hS)]
  rw [he1, he2, hscale, hcross, hcross']
  simp only [energy]
  ring

noncomputable def coefficient (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.powerset.filter (fun S => output S = n)).card

lemma sum_kernel (P : Finset ℕ) (s : ℝ) (a : ℕ) :
    (∑ T ∈ P.powerset, kernel s a (output T)) =
      (coefficient P a : ℝ)*(a : ℝ)^(-(2*s)) := by
  simp only [kernel, eq_comm (a := a)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, coefficient]

/-- The finite energy is exactly the weighted second moment of its fibers. -/
theorem energy_eq_coefficient_sum (P : Finset ℕ) (s : ℝ) :
    energy P s = ∑ n ∈ P.powerset.image output,
      (coefficient P n : ℝ)^2*(n : ℝ)^(-(2*s)) := by
  unfold energy
  simp_rw [sum_kernel]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun S hS => Finset.mem_image_of_mem output hS)]
  apply Finset.sum_congr rfl
  intro n hn
  have he : (∑ S ∈ P.powerset with output S = n,
      (coefficient P (output S) : ℝ)*(output S : ℝ)^(-(2*s))) =
      ∑ S ∈ P.powerset with output S = n,
        (coefficient P n : ℝ)*(n : ℝ)^(-(2*s)) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_filter.mp hS).2]
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (coefficient P n : ℝ)*((coefficient P n : ℝ)*(n : ℝ)^(-(2*s))) = _
  ring

lemma coefficient_le_gSquarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    coefficient P n ≤ gSquarefree n := by
  let F := P.powerset.filter (fun S => output S = n)
  let f : Finset ℕ → ℕ := fun S => ∏ p ∈ S, p
  have hF (S : Finset ℕ) (hS : S ∈ F) : S ⊆ P ∧ output S = n :=
    ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2⟩
  have hinj : Set.InjOn f (F : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have h := congrArg Nat.primeFactors heq
    change (∏ p ∈ S, p).primeFactors = (∏ p ∈ T, p).primeFactors at h
    simpa only [Nat.primeFactors_prod (fun p hp => hP p ((hF S hS).1 hp)),
      Nat.primeFactors_prod (fun p hp => hP p ((hF T hT).1 hp))] using h
  have hsub : (F.image f : Set ℕ) ⊆
      {m : ℕ | Squarefree m ∧ Nat.totient m = n} := by
    intro m hm
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    have hSpr : ∀ p ∈ S, p.Prime := fun p hp => hP p ((hF S hS).1 hp)
    exact ⟨squarefree_prod_of_primes S hSpr,
      (output_eq_totient S hSpr).symm.trans (hF S hS).2⟩
  have hc := Set.ncard_le_ncard hsub (finite_squarefree_totient_fiber n)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at hc
  exact hc

/-- A convergent global squarefree second moment bounds every finite energy. -/
lemma energy_le_squarefree_moment (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℝ)
    (H : Summable (fun n : ℕ => (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s)))) :
    energy P s ≤ ∑' n : ℕ, (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s)) := by
  rw [energy_eq_coefficient_sum]
  apply le_trans (Finset.sum_le_sum (g := fun n : ℕ =>
    (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) ?_) ?_
  · intro n hn
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _
    exact_mod_cast coefficient_le_gSquarefree P hP n
  · exact H.sum_le_tsum _ (fun n _ => by positivity)

lemma correlation_eq_coefficient_sum (P : Finset ℕ) (d : ℕ) (s : ℝ) :
    correlation P d s = ∑ m ∈ P.powerset.image output,
      (coefficient P m : ℝ)*(coefficient P (d*m) : ℝ)*(m : ℝ)^(-(2*s)) := by
  unfold correlation
  rw [Finset.sum_comm]
  have hinner (T : Finset ℕ) :
      (∑ S ∈ P.powerset,
        if output S = d*output T then (output T : ℝ)^(-(2*s)) else 0) =
      (coefficient P (d*output T) : ℝ)*(output T : ℝ)^(-(2*s)) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, coefficient]
  simp_rw [hinner]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun S hS => Finset.mem_image_of_mem output hS)]
  apply Finset.sum_congr rfl
  intro m hm
  have he : (∑ T ∈ P.powerset with output T = m,
      (coefficient P (d*output T) : ℝ)*(output T : ℝ)^(-(2*s))) =
      ∑ T ∈ P.powerset with output T = m,
        (coefficient P (d*m) : ℝ)*(m : ℝ)^(-(2*s)) := by
    apply Finset.sum_congr rfl
    intro T hT
    rw [(Finset.mem_filter.mp hT).2]
  rw [he]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (coefficient P m : ℝ)*((coefficient P (d*m) : ℝ)*(m : ℝ)^(-(2*s))) = _
  ring

lemma coefficient_eq_gSquarefree_of_cover (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hcover : ∀ m : ℕ, Squarefree m → Nat.totient m = n → m.primeFactors ⊆ P) :
    coefficient P n = gSquarefree n := by
  apply le_antisymm (coefficient_le_gSquarefree P hP n)
  let F := (finite_squarefree_totient_fiber n).toFinset
  have hF (m : ℕ) : m ∈ F ↔ Squarefree m ∧ Nat.totient m = n :=
    (finite_squarefree_totient_fiber n).mem_toFinset
  have hinj : Set.InjOn Nat.primeFactors (F : Set ℕ) := by
    intro a ha b hb he
    exact eq_of_totient_eq_of_primeFactors_eq
      (((hF a).mp ha).2.trans (((hF b).mp hb).2.symm)) he
  have hsub : F.image Nat.primeFactors ⊆
      P.powerset.filter (fun S => output S = n) := by
    intro S hS
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hmsf, hmφ⟩ := (hF m).mp hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (hcover m hmsf hmφ), ?_⟩
    rw [output_eq_totient _ (fun q hq => Nat.prime_of_mem_primeFactors hq),
      Nat.prod_primeFactors_of_squarefree hmsf, hmφ]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  have he : F.card = gSquarefree n :=
    (Set.ncard_eq_toFinset_card _ (finite_squarefree_totient_fiber n)).symm
  rw [he] at hcard
  exact hcard

lemma coefficient_eq_zero_of_not_mem (P : Finset ℕ) (n : ℕ)
    (hn : n ∉ P.powerset.image output) : coefficient P n = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact hn (Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1,
    (Finset.mem_filter.mp hS).2⟩)

lemma coefficient_sum_le_energy (P : Finset ℕ) (s : ℝ) (M : Finset ℕ) :
    (∑ n ∈ M, (coefficient P n : ℝ)^2*(n : ℝ)^(-(2*s))) ≤ energy P s := by
  rw [energy_eq_coefficient_sum]
  let R := P.powerset.image output
  have he : (∑ n ∈ M.filter (fun n => n ∈ R),
      (coefficient P n : ℝ)^2*(n : ℝ)^(-(2*s))) =
      ∑ n ∈ M, (coefficient P n : ℝ)^2*(n : ℝ)^(-(2*s)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnnot
    have hnR : n ∉ R := fun h => hnnot (Finset.mem_filter.mpr ⟨hn, h⟩)
    rw [coefficient_eq_zero_of_not_mem P n hnR]
    simp
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n hn hnnot
    positivity

/-- Every finite portion of the unrestricted squarefree moment is realized
inside the energy of a finite set of actual input primes. -/
lemma exists_energy_ge_squarefree_partial_sum (s : ℝ) (M : Finset ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧
      (∑ n ∈ M, (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) ≤ energy P s := by
  let F := fun n => (finite_squarefree_totient_fiber n).toFinset
  let P := M.biUnion (fun n => (F n).biUnion Nat.primeFactors)
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨n, hn, hpF⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hpF
    exact Nat.prime_of_mem_primeFactors hpm
  have hcoeff (n : ℕ) (hn : n ∈ M) : coefficient P n = gSquarefree n := by
    apply coefficient_eq_gSquarefree_of_cover P hP n
    intro m hmsf hmφ p hpm
    apply Finset.mem_biUnion.mpr ⟨n, hn, ?_⟩
    apply Finset.mem_biUnion.mpr ⟨m, ?_, hpm⟩
    exact (finite_squarefree_totient_fiber n).mem_toFinset.mpr ⟨hmsf, hmφ⟩
  refine ⟨P, hP, ?_⟩
  have he : (∑ n ∈ M, (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) =
      ∑ n ∈ M, (coefficient P n : ℝ)^2*(n : ℝ)^(-(2*s)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcoeff n hn]
  rw [he]
  exact coefficient_sum_le_energy P s M

/-- An exact finite-support criterion, not an unconditional boundedness or
unboundedness assertion. -/
theorem summable_squarefree_moment_iff_energy_bounded (s : ℝ) :
    Summable (fun n : ℕ => (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) ↔
      ∃ C : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → energy P s ≤ C := by
  constructor
  · intro H
    exact ⟨∑' n : ℕ, (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s)),
      fun P hP => energy_le_squarefree_moment P hP s H⟩
  · rintro ⟨C, hC⟩
    apply summable_of_sum_le (c := C) (fun n => by positivity)
    intro M
    obtain ⟨P, hP, hsum⟩ := exists_energy_ge_squarefree_partial_sum s M
    exact hsum.trans (hC P hP)

lemma energy_insert_lower (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) (hp1 : 1 < p) (s : ℝ) :
    (1 + ((p-1 : ℕ) : ℝ)^(-(2*s)))*energy P s ≤ energy (insert p P) s := by
  rw [energy_insert P p hp hp1 s]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (correlation_nonneg P (p-1) s))

/-- Discarding the cross terms gives only the diagonal product lower bound. -/
lemma diagonal_product_le_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℝ) :
    (∏ p ∈ P, (1 + ((p-1 : ℕ) : ℝ)^(-(2*s)))) ≤ energy P s := by
  induction P using Finset.induction_on with
  | empty => simp [energy_empty]
  | @insert p P hp ih =>
    have hprime := hP p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp]
    exact (mul_le_mul_of_nonneg_left (ih hrest) (by positivity)).trans
      (energy_insert_lower P p hp hprime.one_lt s)

/-- Above one half, the diagonal product is uniformly bounded over all
finite prime supports. Its lower bound on energy cannot by itself supply
the unboundedness needed for the conjecture. -/
lemma diagonal_product_le_constant (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (s : ℝ) (hs : 1/2 < s) :
    (∏ p ∈ P, (1 + ((p-1 : ℕ) : ℝ)^(-(2*s)))) ≤
      Real.exp (∑' m : ℕ, (Nat.totient m : ℝ)^(-(2*s))) := by
  have H := summable_totient_neg_rpow (2*s) (by linarith)
  have hsum : (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-(2*s))) ≤
      ∑' m : ℕ, (Nat.totient m : ℝ)^(-(2*s)) := by
    have he : (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-(2*s))) =
        ∑ p ∈ P, (Nat.totient p : ℝ)^(-(2*s)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.totient_prime (hP p hp)]
    rw [he]
    exact H.sum_le_tsum _ (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ ∏ p ∈ P, Real.exp (((p-1 : ℕ) : ℝ)^(-(2*s))) := by
      apply Finset.prod_le_prod (fun p hp => by positivity)
      intro p hp
      linarith [Real.add_one_le_exp (((p-1 : ℕ) : ℝ)^(-(2*s)))]
    _ = Real.exp (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-(2*s))) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

/-- The unbounded finite-energy statement is an exact reformulation. The
right-hand side is not established by the insertion identity alone. -/
theorem erdos_821_iff_energy_unbounded :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
      ∀ s : ℝ, 1/2 < s → s < 1 → ∀ C : ℝ,
        ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ C < energy P s := by
  rw [PrimitiveCollisions.erdos_821_iff_primitive_collision_divergence]
  constructor
  · intro H s hs hs1 C
    by_contra hnone
    push_neg at hnone
    have Hsf := (summable_squarefree_moment_iff_energy_bounded s).mpr ⟨C, hnone⟩
    exact H s hs hs1
      ((PrimitiveCollisions.summable_squarefree_second_moment_iff s hs).mp Hsf)
  · intro H s hs hs1 Hprim
    have Hsf := (PrimitiveCollisions.summable_squarefree_second_moment_iff s hs).mpr Hprim
    obtain ⟨C, hC⟩ := (summable_squarefree_moment_iff_energy_bounded s).mp Hsf
    obtain ⟨P, hP, hbig⟩ := H s hs hs1 C
    exact (not_lt_of_ge (hC P hP)) hbig

end Erdos821.FiniteEnergy
