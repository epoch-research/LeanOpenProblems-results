import FormalConjecturesUtil

/-! A structured special case for sets with finite dyadic kernel.
This file does not settle the unrestricted conjecture. -/

namespace Erdos3FiniteKernelCase

set_option maxHeartbeats 1000000

open scoped Classical

def sectionSet (A : Set ℕ) (q r : ℕ) : Set ℕ := {n | q * n + r ∈ A}

def dyadicKernel (A : Set ℕ) : Set (Set ℕ) :=
  {B | ∃ m r : ℕ, r < 2 ^ m ∧ B = sectionSet A (2 ^ m) r}

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

lemma self_mem_kernel (A : Set ℕ) : A ∈ dyadicKernel A := by
  refine ⟨0, 0, by norm_num, ?_⟩
  ext n
  simp [sectionSet]

lemma section_section (A : Set ℕ) (p r q s : ℕ) :
    sectionSet (sectionSet A p r) q s = sectionSet A (p * q) (p * s + r) := by
  ext n
  simp only [sectionSet, Set.mem_setOf_eq]
  rw [show p * (q * n + s) + r = p * q * n + (p * s + r) by ring]

lemma kernel_closed {A B : Set ℕ} (hB : B ∈ dyadicKernel A) {m r : ℕ}
    (hr : r < 2 ^ m) : sectionSet B (2 ^ m) r ∈ dyadicKernel A := by
  obtain ⟨l, s, hs, rfl⟩ := hB
  refine ⟨l + m, 2 ^ l * r + s, ?_, ?_⟩
  · rw [pow_add]
    have h := Nat.mul_le_mul_left (2 ^ l) (Nat.succ_le_of_lt hr)
    nlinarith
  · rw [section_section, pow_add]

lemma HasAP.of_section {A : Set ℕ} {q r k : ℕ} (hq : 0 < q)
    (h : HasAP (sectionSet A q r) k) : HasAP A k := by
  obtain ⟨a, d, hd, hmem⟩ := h
  refine ⟨q * a + r, q * d, Nat.mul_pos hq hd, fun i hi ↦ ?_⟩
  have h := hmem i hi
  change q * (a + i * d) + r ∈ A at h
  rw [show q * a + r + i * (q * d) = q * (a + i * d) + r by ring]
  exact h

/-- A finite van der Waerden bound obtained from Hales--Jewett. -/
lemma finite_vdw (κ : Type*) [Finite κ] (k : ℕ) :
    ∃ N : ℕ, ∀ color : ℕ → κ, ∃ a d : ℕ, ∃ c : κ,
      0 < d ∧ ∀ i ≤ k, a + i * d < N ∧ color (a + i * d) = c := by
  classical
  obtain ⟨n, hn⟩ :=
    Combinatorics.Subspace.exists_mono_in_high_dimension_fin (Fin (k + 1)) κ Unit
  refine ⟨n * (k + 1) + 1, fun color ↦ ?_⟩
  obtain ⟨l, c, hc⟩ := hn (fun v ↦ color (∑ i : Fin n, (v i : ℕ)))
  let u : Fin n → ℕ := fun i ↦ (l.idxFun i).elim (fun x ↦ x.val) (fun _ ↦ 0)
  let v : Fin n → ℕ := fun i ↦ (l.idxFun i).elim (fun _ ↦ 0) (fun _ ↦ 1)
  let a := ∑ i : Fin n, u i
  let d := ∑ i : Fin n, v i
  have hd : 0 < d := by
    obtain ⟨i, hi⟩ := l.proper ()
    have hle := Finset.single_le_sum (s := Finset.univ) (f := v)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hv : v i = 1 := by simp [v, hi]
    rw [hv] at hle
    exact lt_of_lt_of_le (by omega : 0 < 1) hle
  have hlin (j : Fin (k + 1)) : (∑ i : Fin n, (l (fun _ ↦ j) i : ℕ)) = a + j.val * d := by
    calc
      _ = ∑ i : Fin n, (u i + j.val * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        cases h : l.idxFun i <;> simp [Combinatorics.Subspace.coe_apply, u, v, h]
      _ = _ := by simp [a, d, Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨a, d, c, hd, fun i hi ↦ ?_⟩
  let j : Fin (k + 1) := ⟨i, by omega⟩
  have hbound : (∑ x : Fin n, (l (fun _ ↦ j) x : ℕ)) ≤ n * (k + 1) := by
    calc
      _ ≤ ∑ _x : Fin n, (k + 1) :=
        Finset.sum_le_sum (fun x _ ↦ (l (fun _ ↦ j) x).isLt.le)
      _ = _ := by simp
  rw [hlin] at hbound
  refine ⟨by dsimp [j] at hbound; omega, ?_⟩
  have hcolor := hc (fun _ ↦ j)
  change color (∑ x : Fin n, (l (fun _ ↦ j) x : ℕ)) = c at hcolor
  rw [hlin] at hcolor
  exact hcolor

lemma kernel_noAP {A B : Set ℕ} {k : ℕ} (hA : ¬ HasAP A k)
    (hB : B ∈ dyadicKernel A) : ¬ HasAP B k := by
  obtain ⟨m, r, hr, rfl⟩ := hB
  intro h
  exact hA (h.of_section (by positivity))

/-- Finite kernel plus AP-freeness gives a uniformly bounded missing residue section. -/
lemma uniform_holes_of_finite_kernel {A : Set ℕ} {k : ℕ}
    (hK : (dyadicKernel A).Finite) (hA : ¬ HasAP A k) :
    ∃ L : ℕ, 0 < L ∧ ∀ B ∈ dyadicKernel A, ∃ r < 2 ^ L,
      sectionSet B (2 ^ L) r = ∅ := by
  classical
  letI := hK.fintype
  obtain ⟨N, hN⟩ := finite_vdw (dyadicKernel A) k
  let L := N + 1
  have hbig : N < 2 ^ L := (Nat.lt_succ_self N).trans Nat.lt_two_pow_self
  have hQ : 0 < 2 ^ L := by positivity
  refine ⟨L, by dsimp [L]; omega, fun B hB ↦ ?_⟩
  by_contra! h
  let color : ℕ → dyadicKernel A := fun r ↦
    ⟨sectionSet B (2 ^ L) (r % (2 ^ L)), kernel_closed hB (Nat.mod_lt r hQ)⟩
  obtain ⟨a, d, c, hd, hmono⟩ := hN color
  have haN : a < N := by simpa using (hmono 0 (by omega)).1
  have haQ : a < 2 ^ L := haN.trans hbig
  obtain ⟨t, ht⟩ := h a haQ
  apply kernel_noAP hA hB
  refine ⟨2 ^ L * t + a, d, hd, fun i hi ↦ ?_⟩
  have hiQ : a + i * d < 2 ^ L := ((hmono i hi.le).1).trans hbig
  have hcol : color (a + i * d) = color a :=
    (hmono i hi.le).2.trans (by simpa using (hmono 0 (by omega)).2.symm)
  have hsec : sectionSet B (2 ^ L) (a + i * d) = sectionSet B (2 ^ L) a := by
    have hh := congrArg Subtype.val hcol
    simpa only [color, Nat.mod_eq_of_lt hiQ, Nat.mod_eq_of_lt haQ] using hh
  have ht' : t ∈ sectionSet B (2 ^ L) (a + i * d) := by rw [hsec]; exact ht
  simpa only [sectionSet, Set.mem_setOf_eq, Nat.add_assoc] using ht'

noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ i : Fin N, if i.val ∈ A then 1 else 0

lemma count_eq_card (A : Set ℕ) (N : ℕ) :
    count A N = ((Finset.range N).filter (fun n ↦ n ∈ A)).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  rfl

lemma count_le (A : Set ℕ) (N : ℕ) : count A N ≤ N := by
  classical
  calc
    count A N ≤ ∑ _i : Fin N, (1 : ℕ) := Finset.sum_le_sum (fun i _ ↦ by split <;> omega)
    _ = N := by simp

lemma count_empty (N : ℕ) : count ∅ N = 0 := by simp [count]

lemma count_mul (A : Set ℕ) (Q N : ℕ) :
    count A (N * Q) = ∑ r : Fin Q, count (sectionSet A Q r.val) N := by
  classical
  unfold count
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type, Finset.sum_comm]
  simp [finProdFinEquiv, sectionSet, Nat.add_comm]

lemma count_pow_le_of_holes (K : Set (Set ℕ)) (Q : ℕ)
    (hclosed : ∀ B ∈ K, ∀ r < Q, sectionSet B Q r ∈ K)
    (hholes : ∀ B ∈ K, ∃ r < Q, sectionSet B Q r = ∅) :
    ∀ j : ℕ, ∀ B ∈ K, count B (Q ^ j) ≤ (Q - 1) ^ j := by
  intro j
  induction j with
  | zero => intro B hB; simpa using count_le B 1
  | succ j ih =>
    intro B hB
    obtain ⟨r, hr, hempty⟩ := hholes B hB
    let rr : Fin Q := ⟨r, hr⟩
    have hzero : count (sectionSet B Q rr.val) (Q ^ j) = 0 := by
      rw [hempty, count_empty]
    rw [pow_succ, count_mul]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ rr), hzero, add_zero]
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin Q)).erase rr, (Q - 1) ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        exact ih _ (hclosed B hB i.val i.isLt)
      _ = (Q - 1) ^ (j + 1) := by simp [pow_succ, mul_comm]

lemma card_le_count {A : Set ℕ} {N : ℕ} {S : Finset ℕ}
    (hSA : (S : Set ℕ) ⊆ A) (hN : ∀ n ∈ S, n < N) : S.card ≤ count A N := by
  rw [count_eq_card]
  apply Finset.card_le_card
  intro n hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hN n hn), hSA hn⟩

/-- Uniform geometric loss in residue counts implies reciprocal summability. -/
lemma summable_of_count_pow_bound {A : Set ℕ} {Q : ℕ} (hQ : 1 < Q)
    (hcount : ∀ j : ℕ, count A (Q ^ j) ≤ (Q - 1) ^ j) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let R : ℝ := ((Q - 1 : ℕ) : ℝ) / (Q : ℝ)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by
    apply (div_lt_one hQr).mpr
    exact_mod_cast (show Q - 1 < Q by omega)
  have hgeo : Summable (fun j : ℕ ↦ ((Q - 1 : ℕ) : ℝ) * R ^ j) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left _
  have hfinite : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ A →
      (∑ n ∈ S, 1 / (n : ℝ)) ≤ ∑' j : ℕ, ((Q - 1 : ℕ) : ℝ) * R ^ j := by
    intro S hSA
    let S' := S.erase 0
    let J := S'.image (Nat.log Q)
    have hfiber (j : ℕ) :
        (∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ)) ≤
          ((Q - 1 : ℕ) : ℝ) * R ^ j := by
      let T := S'.filter (fun n ↦ Nat.log Q n = j)
      have hTsub : (T : Set ℕ) ⊆ A := by
        intro n hn
        exact hSA ((Finset.erase_subset _ _) ((Finset.filter_subset _ _) hn))
      have hTb : ∀ n ∈ T, n < Q ^ (j + 1) := by
        intro n hn
        obtain ⟨_, hnj⟩ := Finset.mem_filter.mp hn
        simpa [hnj] using Nat.lt_pow_succ_log_self hQ n
      have hTc : T.card ≤ (Q - 1) ^ (j + 1) :=
        (card_le_count hTsub hTb).trans (hcount (j + 1))
      calc
        (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((Q ^ j : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
          have hn0 := (Finset.mem_erase.mp hnS).1
          have hpow : Q ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self Q hn0
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow)
        _ = (T.card : ℝ) / ((Q ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
        _ ≤ (((Q - 1) ^ (j + 1) : ℕ) : ℝ) / ((Q ^ j : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast hTc
        _ = ((Q - 1 : ℕ) : ℝ) * R ^ j := by
          dsimp [R]
          rw [Nat.cast_pow, Nat.cast_pow, div_pow, pow_succ]
          ring
    calc
      (∑ n ∈ S, 1 / (n : ℝ)) = ∑ n ∈ S', 1 / (n : ℝ) :=
        (Finset.sum_erase S (by simp : (1 : ℝ) / (0 : ℕ) = 0)).symm
      _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun n hn ↦ Finset.mem_image_of_mem (Nat.log Q) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑ j ∈ J, ((Q - 1 : ℕ) : ℝ) * R ^ j :=
        Finset.sum_le_sum (fun j _ ↦ hfiber j)
      _ ≤ _ := Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hgeo
  apply summable_of_sum_le (c := ∑' j : ℕ, ((Q - 1 : ℕ) : ℝ) * R ^ j)
    (fun _ ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  simpa [e] using hfinite (F.map e) hsub

/-- A fixed AP-length obstruction forces summability when the dyadic kernel is finite. -/
theorem finite_kernel_noAP_summable {A : Set ℕ} {k : ℕ}
    (hK : (dyadicKernel A).Finite) (hA : ¬ HasAP A k) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  obtain ⟨L, hL, hholes⟩ := uniform_holes_of_finite_kernel hK hA
  have hQ : 1 < 2 ^ L := one_lt_pow₀ one_lt_two (Nat.ne_of_gt hL)
  apply summable_of_count_pow_bound hQ
  intro j
  exact count_pow_le_of_holes (dyadicKernel A) (2 ^ L)
    (fun B hB r hr ↦ kernel_closed hB hr) hholes j A (self_mem_kernel A)

theorem finite_kernel_contains_ap {A : Set ℕ} (hK : (dyadicKernel A).Finite)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (k : ℕ) :
    ∃ S ⊆ A, S.IsAPOfLength k := by
  have hAP : HasAP A k := by
    by_contra h
    exact hs (finite_kernel_noAP_summable hK h)
  obtain ⟨a, d, hd, hmem⟩ := hAP
  let g : ℕ → ℕ := fun i ↦ a + i * d
  have hgi : Function.Injective g := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  refine ⟨g '' Set.Iio k, ?_, a, d, ?_, ?_⟩
  · rintro x ⟨i, hi, rfl⟩
    exact hmem i hi
  · change (g '' Set.Iio k).encard = (k : ℕ∞)
    rw [hgi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [g]

/-- The exact original conclusion with the extra finite-dyadic-kernel hypothesis. -/
theorem finite_kernel_case {A : Set ℕ} (hK : (dyadicKernel A).Finite)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ᶠ (k : ℕ) in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength k := by
  apply Filter.frequently_atTop.mpr
  intro k
  exact ⟨k, le_rfl, finite_kernel_contains_ap hK hs k⟩

def FiniteShiftIntersections (A : Set ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → {x : ℕ | x ∈ A ∧ x + d ∈ A}.Finite

lemma finite_shift_kernel {A B : Set ℕ} (hA : FiniteShiftIntersections A)
    (hB : B ∈ dyadicKernel A) : FiniteShiftIntersections B := by
  obtain ⟨m, r, hr, rfl⟩ := hB
  intro d hd
  let f : ℕ → ℕ := fun x ↦ 2 ^ m * x + r
  have hf : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    have hp : 0 < 2 ^ m := by positivity
    nlinarith
  have hfin := (hA (2 ^ m * d) (Nat.mul_pos (by positivity) hd)).preimage hf.injOn
  apply hfin.subset
  rintro x ⟨hx, hy⟩
  refine ⟨hx, ?_⟩
  change 2 ^ m * (x + d) + r ∈ A at hy
  change 2 ^ m * x + r + 2 ^ m * d ∈ A
  convert hy using 1; ring

lemma uniform_finite_holes {A : Set ℕ} (hK : (dyadicKernel A).Finite)
    (hA : FiniteShiftIntersections A) :
    ∃ L : ℕ, 0 < L ∧ ∀ B ∈ dyadicKernel A, ∃ r < 2 ^ L,
      (sectionSet B (2 ^ L) r).Finite := by
  classical
  letI := hK.fintype
  obtain ⟨N, hN⟩ := finite_vdw (dyadicKernel A) 1
  let L := N + 1
  have hbig : N < 2 ^ L := (Nat.lt_succ_self N).trans Nat.lt_two_pow_self
  have hQ : 0 < 2 ^ L := by positivity
  refine ⟨L, by dsimp [L]; omega, fun B hB ↦ ?_⟩
  let color : ℕ → dyadicKernel A := fun r ↦
    ⟨sectionSet B (2 ^ L) (r % (2 ^ L)), kernel_closed hB (Nat.mod_lt r hQ)⟩
  obtain ⟨a, d, c, hd, hmono⟩ := hN color
  have haN : a < N := by simpa using (hmono 0 (by omega)).1
  have hadN : a + d < N := by simpa using (hmono 1 (by omega)).1
  have haQ : a < 2 ^ L := haN.trans hbig
  have hadQ : a + d < 2 ^ L := hadN.trans hbig
  have hcol : color (a + d) = color a := by
    have h0 := (hmono 0 (by omega)).2
    have h1 := (hmono 1 (by omega)).2
    simpa using h1.trans h0.symm
  have hsec : sectionSet B (2 ^ L) (a + d) = sectionSet B (2 ^ L) a := by
    have hh := congrArg Subtype.val hcol
    simpa only [color, Nat.mod_eq_of_lt hadQ, Nat.mod_eq_of_lt haQ] using hh
  let f : ℕ → ℕ := fun x ↦ 2 ^ L * x + a
  have hf : Function.Injective f := by intro x y h; dsimp [f] at h; nlinarith
  have hfin := ((finite_shift_kernel hA hB) d hd).preimage hf.injOn
  refine ⟨a, haQ, hfin.subset ?_⟩
  intro t ht
  refine ⟨ht, ?_⟩
  have ht' : t ∈ sectionSet B (2 ^ L) (a + d) := by rw [hsec]; exact ht
  simpa only [sectionSet, Set.mem_setOf_eq, f, Nat.add_assoc] using ht'

lemma count_le_ncard {B : Set ℕ} (hB : B.Finite) (N : ℕ) : count B N ≤ B.ncard := by
  rw [count_eq_card, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ hB
  intro n hn
  have hh : n ∈ Finset.range N ∧ n ∈ B := by
    simpa only [Finset.mem_coe, Finset.mem_filter] using hn
  exact hh.2

lemma count_pow_le_of_finite_holes (K : Set (Set ℕ)) (Q M : ℕ) (hQ : 1 < Q)
    (hclosed : ∀ B ∈ K, ∀ r < Q, sectionSet B Q r ∈ K)
    (hholes : ∀ B ∈ K, ∃ r < Q, ∀ N, count (sectionSet B Q r) N ≤ M) :
    ∀ j : ℕ, ∀ B ∈ K, count B (Q ^ j) ≤ (M + 1) * (j + 1) * (Q - 1) ^ j := by
  intro j
  induction j with
  | zero =>
    intro B hB
    have h := count_le B 1
    simpa using h.trans (show 1 ≤ M + 1 by omega)
  | succ j ih =>
    intro B hB
    obtain ⟨r, hr, hsmall⟩ := hholes B hB
    let rr : Fin Q := ⟨r, hr⟩
    rw [pow_succ, count_mul, ← Finset.sum_erase_add _ _ (Finset.mem_univ rr)]
    have hsum : (∑ i ∈ (Finset.univ : Finset (Fin Q)).erase rr,
        count (sectionSet B Q i.val) (Q ^ j)) ≤
          (Q - 1) * ((M + 1) * (j + 1) * (Q - 1) ^ j) := by
      calc
        _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin Q)).erase rr,
            (M + 1) * (j + 1) * (Q - 1) ^ j := by
          apply Finset.sum_le_sum
          intro i hi
          exact ih _ (hclosed B hB i.val i.isLt)
        _ = _ := by simp
    have hp : 1 ≤ (Q - 1) ^ j := one_le_pow₀ (by omega)
    have hB : 1 ≤ Q - 1 := by omega
    calc
      _ ≤ (Q - 1) * ((M + 1) * (j + 1) * (Q - 1) ^ j) + M :=
        Nat.add_le_add hsum (hsmall (Q ^ j))
      _ ≤ (M + 1) * (j + 1 + 1) * (Q - 1) ^ (j + 1) := by
        have h1 : M + 1 ≤ (M + 1) * (Q - 1) ^ j := by
          simpa using Nat.mul_le_mul_left (M + 1) hp
        have h2 : (M + 1) * (Q - 1) ^ j ≤ (M + 1) * (Q - 1) ^ j * (Q - 1) := by
          simpa using Nat.mul_le_mul_left ((M + 1) * (Q - 1) ^ j) hB
        calc
          _ ≤ (Q - 1) * ((M + 1) * (j + 1) * (Q - 1) ^ j) +
              (M + 1) * (Q - 1) ^ j * (Q - 1) := by omega
          _ = _ := by rw [pow_succ]; ring

lemma summable_of_scaled_count_bound {A : Set ℕ} {Q : ℕ} (hQ : 1 < Q)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (hs : Summable f)
    (hcount : ∀ j, (count A (Q ^ (j + 1)) : ℝ) ≤ f j * (Q : ℝ) ^ j) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hfinite : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ A →
      (∑ n ∈ S, 1 / (n : ℝ)) ≤ ∑' j : ℕ, f j := by
    intro S hSA
    let S' := S.erase 0
    let J := S'.image (Nat.log Q)
    have hfiber (j : ℕ) :
        (∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ)) ≤ f j := by
      let T := S'.filter (fun n ↦ Nat.log Q n = j)
      have hTsub : (T : Set ℕ) ⊆ A := by
        intro n hn
        exact hSA ((Finset.erase_subset _ _) ((Finset.filter_subset _ _) hn))
      have hTb : ∀ n ∈ T, n < Q ^ (j + 1) := by
        intro n hn
        obtain ⟨_, hnj⟩ := Finset.mem_filter.mp hn
        simpa [hnj] using Nat.lt_pow_succ_log_self hQ n
      have hTc : (T.card : ℝ) ≤ f j * (Q : ℝ) ^ j :=
        (show (T.card : ℝ) ≤ count A (Q ^ (j + 1)) by
          exact_mod_cast card_le_count hTsub hTb).trans (hcount j)
      calc
        (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((Q ^ j : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
          have hn0 := (Finset.mem_erase.mp hnS).1
          have hpow : Q ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self Q hn0
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow)
        _ = (T.card : ℝ) / ((Q ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
        _ ≤ (f j * (Q : ℝ) ^ j) / ((Q ^ j : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hTc (by positivity)
        _ = f j := by simp [Nat.cast_pow, ne_of_gt hQr]
    calc
      (∑ n ∈ S, 1 / (n : ℝ)) = ∑ n ∈ S', 1 / (n : ℝ) :=
        (Finset.sum_erase S (by simp : (1 : ℝ) / (0 : ℕ) = 0)).symm
      _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log Q n = j), 1 / (n : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun n hn ↦ Finset.mem_image_of_mem (Nat.log Q) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
      _ ≤ ∑ j ∈ J, f j := Finset.sum_le_sum (fun j _ ↦ hfiber j)
      _ ≤ _ := Summable.sum_le_tsum _ (fun j _ ↦ hf j) hs
  apply summable_of_sum_le (c := ∑' j : ℕ, f j) (fun _ ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  simpa [e] using hfinite (F.map e) hsub

theorem finite_kernel_finite_shift_summable {A : Set ℕ}
    (hK : (dyadicKernel A).Finite) (hA : FiniteShiftIntersections A) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  classical
  obtain ⟨L, hL, hholes⟩ := uniform_finite_holes hK hA
  let Q := 2 ^ L
  have hQ : 1 < Q := one_lt_pow₀ one_lt_two (Nat.ne_of_gt hL)
  let M := ∑ B ∈ hK.toFinset, B.ncard
  have hholes' : ∀ B ∈ dyadicKernel A, ∃ r < Q,
      ∀ N, count (sectionSet B Q r) N ≤ M := by
    intro B hB
    obtain ⟨r, hr, hfin⟩ := hholes B hB
    refine ⟨r, hr, fun N ↦ (count_le_ncard hfin N).trans ?_⟩
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (hK.mem_toFinset.mpr (kernel_closed hB hr))
  have hcount : ∀ j, count A (Q ^ j) ≤ (M + 1) * (j + 1) * (Q - 1) ^ j := by
    intro j
    exact count_pow_le_of_finite_holes (dyadicKernel A) Q M hQ
      (fun B hB r hr ↦ kernel_closed hB hr) hholes' j A (self_mem_kernel A)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let R : ℝ := ((Q - 1 : ℕ) : ℝ) / (Q : ℝ)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by
    apply (div_lt_one hQr).mpr
    exact_mod_cast (show Q - 1 < Q by omega)
  have hgeo := summable_geometric_of_lt_one hR0 hR1
  have hj : Summable (fun j : ℕ ↦ (j : ℝ) * R ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := R) (by simpa [Real.norm_eq_abs, abs_of_nonneg hR0] using hR1)
  have hp : Summable (fun j : ℕ ↦ ((j : ℝ) + 2) * R ^ j) := by
    simpa only [add_mul] using hj.add (hgeo.mul_left 2)
  let f : ℕ → ℝ := fun j ↦ ((M + 1 : ℕ) : ℝ) * ((Q - 1 : ℕ) : ℝ) * ((j : ℝ) + 2) * R ^ j
  have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity
  have hs : Summable f := by
    simpa only [f, mul_assoc] using hp.mul_left (((M + 1 : ℕ) : ℝ) * ((Q - 1 : ℕ) : ℝ))
  apply summable_of_scaled_count_bound hQ f hf hs
  intro j
  have hc : (count A (Q ^ (j + 1)) : ℝ) ≤
      ((M + 1 : ℕ) : ℝ) * ((j : ℝ) + 2) * ((Q - 1 : ℕ) : ℝ) ^ (j + 1) := by
    exact_mod_cast hcount (j + 1)
  calc
    _ ≤ _ := hc
    _ = f j * (Q : ℝ) ^ j := by
      dsimp [f, R]
      rw [pow_succ, div_pow]
      field_simp

/-- A divergent finite-kernel set must have infinite recurrence at some fixed shift. -/
theorem finite_kernel_infinite_shift {A : Set ℕ} (hK : (dyadicKernel A).Finite)
    (hs : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) :
    ∃ d : ℕ, 0 < d ∧ {x : ℕ | x ∈ A ∧ x + d ∈ A}.Infinite := by
  by_contra! h
  exact hs (finite_kernel_finite_shift_summable hK h)

theorem finite_kernel_subset_summable {A B : Set ℕ} (hA : FiniteShiftIntersections A)
    (hBA : B ⊆ A) (hB : (dyadicKernel B).Finite) :
    Summable (fun b : B ↦ 1 / (b : ℝ)) := by
  apply finite_kernel_finite_shift_summable hB
  intro d hd
  exact (hA d hd).subset (fun x hx ↦ ⟨hBA hx.1, hBA hx.2⟩)

#print axioms finite_kernel_subset_summable
#print axioms finite_kernel_infinite_shift
#print axioms count_pow_le_of_finite_holes
#print axioms uniform_finite_holes
#print axioms finite_kernel_case
#print axioms finite_kernel_noAP_summable
#print axioms summable_of_count_pow_bound
#print axioms count_pow_le_of_holes
#print axioms count_mul
#print axioms uniform_holes_of_finite_kernel
#print axioms finite_vdw

end Erdos3FiniteKernelCase
