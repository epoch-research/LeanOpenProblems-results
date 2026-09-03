import FormalConjecturesUtil

/-!
# Erdős Problem 1

*Reference:* [erdosproblems.com/1](https://www.erdosproblems.com/1)
-/

open Filter

open scoped Topology Real

namespace Erdos1

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/- The following are auxiliary bounds and reformulations.
They do not prove the uniform estimate in `erdos_1`. -/

theorem counting_bound {A : Finset ℕ} {N : ℕ} (h : IsSumDistinctSet A N) :
    2 ^ A.card ≤ A.card * N + 1 := by
  have hsum (S : Finset ℕ) (hS : S ∈ A.powerset) : S.sum id ≤ A.card * N := by
    have hsub : S ⊆ A := Finset.mem_powerset.mp hS
    calc
      S.sum id ≤ S.card * N := by
        simpa using Finset.sum_le_card_nsmul S id N
          (fun x hx => (Finset.mem_Icc.mp (h.1 (hsub hx))).2)
      _ ≤ A.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hsub)
  have hc : A.powerset.card ≤ (Finset.Icc 0 (A.card * N)).card :=
    Finset.card_le_card_of_injOn (fun S : Finset ℕ => S.sum id)
      (fun S hS => Finset.mem_Icc.mpr ⟨Nat.zero_le _, hsum S hS⟩)
      (fun S hS T hT heq => congrArg Subtype.val
        (@h.2 ⟨S, hS⟩ ⟨T, hT⟩ heq))
  simpa using hc

theorem counting_bound_total_sum (A : Finset ℕ)
    (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    2 ^ A.card ≤ A.sum id + 1 := by
  have hc : A.powerset.card ≤ (Finset.Icc 0 (A.sum id)).card :=
    Finset.card_le_card_of_injOn (fun S : Finset ℕ => S.sum id)
      (fun S hS => Finset.mem_Icc.mpr ⟨Nat.zero_le _,
        Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp hS)⟩)
      (fun S hS T hT heq => congrArg Subtype.val
        (@h ⟨S, hS⟩ ⟨T, hT⟩ heq))
  simpa using hc


theorem centered_sum_sq {α : Type*} (A : Finset α) (f : α → ℝ) :
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, f a) - ∑ a ∈ A, f a) ^ 2 =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (f a) ^ 2 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha]
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hins (S : Finset α) (hS : S ∈ A.powerset) :
        ∑ x ∈ insert a S, f x = f a + ∑ x ∈ S, f x := by
      exact Finset.sum_insert (fun h => ha (Finset.mem_powerset.mp hS h))
    simp_rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ S ∈ A.powerset,
          (2 * (2 * (∑ x ∈ S, f x) - ∑ x ∈ A, f x) ^ 2 + 2 * f a ^ 2) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [hins S hS]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]
        simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
          Nat.cast_pow, Nat.cast_ofNat, pow_succ]
        ring

theorem variance_lower_bound (S : Finset ℕ) (c : ℝ) :
    (S.card : ℝ) * ((S.card : ℝ) ^ 2 - 1) ≤
      12 * ∑ x ∈ S, ((x : ℝ) - c) ^ 2 := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hnonneg : 0 ≤ ∑ x ∈ S, ((x : ℝ) - c) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    by_cases hsmall : S.card ≤ 1
    · have hcard : (S.card : ℝ) ≤ 1 := by exact_mod_cast hsmall
      have hcard0 : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
      have hsq : (S.card : ℝ) ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hcard0 (sub_nonpos.mpr hsq)]
    · have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      let a := S.min' hne
      let b := S.max' hne
      have ha : a ∈ S := S.min'_mem hne
      have hb : b ∈ S := S.max'_mem hne
      have hab : a ≤ b := S.min'_le b hb
      have hspan : S.card ≤ b + 1 - a := by
        have hsub : S ⊆ Finset.Icc a b := fun x hx =>
          Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
        simpa using Finset.card_le_card hsub
      have hab' : a < b := by omega
      have hbe : b ∈ S.erase a := Finset.mem_erase.mpr ⟨by omega, hb⟩
      let T := (S.erase a).erase b
      have hTcard : T.card + 2 = S.card := by
        simp only [T, Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha]
        omega
      have hTcardR : (T.card : ℝ) + 2 = (S.card : ℝ) := by exact_mod_cast hTcard
      have hTlt : T ⊂ S  := Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset b _) (Finset.erase_ssubset ha)
      have hrec := ih T hTlt
      have hsum : ∑ x ∈ S, ((x : ℝ) - c) ^ 2 =
          (∑ x ∈ T, ((x : ℝ) - c) ^ 2) + ((b : ℝ) - c) ^ 2 + ((a : ℝ) - c) ^ 2 := by
        rw [← Finset.sum_erase_add S (fun x => ((x : ℝ) - c) ^ 2) ha,
          ← Finset.sum_erase_add (S.erase a) (fun x => ((x : ℝ) - c) ^ 2) hbe]
      have hspanR : (S.card : ℝ) - 1 ≤ (b : ℝ) - a := by
        have hn : S.card + a ≤ b + 1 := by omega
        have hr : (S.card : ℝ) + a ≤ b + 1 := by exact_mod_cast hn
        linarith
      have hcardR : 2 ≤ (S.card : ℝ) := by exact_mod_cast (show 2 ≤ S.card by omega)
      have hgap : ((S.card : ℝ) - 1) ^ 2 ≤ ((b : ℝ) - a) ^ 2 := by
        apply (sq_le_sq₀ (by linarith) (by linarith)).mpr hspanR
      rw [hsum, ← hTcardR]
      rw [← hTcardR] at hgap
      nlinarith only [hgap, hrec, sq_nonneg ((a : ℝ) + b - 2 * c)]

theorem sum_sq_bound (A : Finset ℕ)
    (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    ((2 : ℝ) ^ A.card) ^ 2 ≤ 3 * (∑ a ∈ A, (a : ℝ) ^ 2) + 1 := by
  have hinj : Set.InjOn (fun S : Finset ℕ => S.sum id) A.powerset := by
    intro S hS T hT heq
    exact congrArg Subtype.val (@h ⟨S, hS⟩ ⟨T, hT⟩ heq)
  let c : ℝ := (∑ a ∈ A, (a : ℝ)) / 2
  have hlo := variance_lower_bound (A.powerset.image (fun S => S.sum id)) c
  rw [Finset.card_image_of_injOn hinj, Finset.card_powerset,
    Finset.sum_image hinj] at hlo
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum, id_eq] at hlo
  have hvariance : 4 * (∑ S ∈ A.powerset, ((∑ a ∈ S, (a : ℝ)) - c) ^ 2) =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← centered_sum_sq A (fun a => (a : ℝ))]
    apply Finset.sum_congr rfl
    intro S hS
    dsimp [c]
    ring
  have hp : 0 < (2 : ℝ) ^ A.card := by positivity
  have hprod : (2 : ℝ) ^ A.card * (((2 : ℝ) ^ A.card) ^ 2 - 1) ≤
      (2 : ℝ) ^ A.card * (3 * ∑ a ∈ A, (a : ℝ) ^ 2) := by
    nlinarith only [hlo, hvariance]
  have hcancel := (mul_le_mul_iff_right₀ hp).mp hprod
  linarith

theorem second_moment_bound (A : Finset ℕ) (N : ℕ)
    (hbound : A ⊆ Finset.Icc 1 N)
    (h : (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) :
    ((2 : ℝ) ^ A.card) ^ 2 ≤ 3 * A.card * (N : ℝ) ^ 2 + 1 := by
  have hs := sum_sq_bound A h
  have hu : (∑ a ∈ A, (a : ℝ) ^ 2) ≤ (A.card : ℝ) * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, (N : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hb : (a : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp (hbound ha)).2
        exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hb
      _ = _ := by simp
  nlinarith


theorem uniform_bound_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → 2 ^ A.card ≤ K * N) := by
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / C)
    refine ⟨K, fun N A hA hN => ?_⟩
    have hKC : 1 < (K : ℝ) * C := (div_lt_iff₀ hC).mp hK
    have hKN : 0 < (K : ℝ) := lt_trans (one_div_pos.mpr hC) hK
    have hCN := h N A hA hN
    have hmul := mul_lt_mul_of_pos_left hCN hKN
    have hp : 0 < (2 : ℝ) ^ A.card := by positivity
    have hp' := mul_lt_mul_of_pos_right hKC hp
    have hr : (2 : ℝ) ^ A.card ≤ (K : ℝ) * N := by nlinarith only [hmul, hp']
    exact_mod_cast hr
  · rintro ⟨K, hK⟩
    refine ⟨1 / ((K : ℝ) + 1), by positivity, fun N A hA hN => ?_⟩
    have hb : (2 : ℝ) ^ A.card ≤ (K : ℝ) * N := by
      exact_mod_cast hK N A hA hN
    have hN' : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hden : 0 < (K : ℝ) + 1 := by positivity
    rw [one_div_mul_eq_div, div_lt_iff₀ hden]
    nlinarith

theorem negation_iff :
    (¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∀ K : ℕ, ∃ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N ∧
      N ≠ 0 ∧ K * N < 2 ^ A.card) := by
  rw [uniform_bound_iff]
  push_neg
  rfl


/-- A disproof must supply examples beyond every cardinality and size threshold. -/
theorem negation_large_iff :
    (¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∀ K n₀ N₀ : ℕ, ∃ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N ∧
      N ≠ 0 ∧ n₀ < A.card ∧ N₀ < N ∧ K * N < 2 ^ A.card) := by
  rw [negation_iff]
  constructor
  · intro h K n₀ N₀
    obtain ⟨N, A, hA, hN, hlt⟩ := h (K + 2 ^ max n₀ N₀)
    have hpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hlarge : max n₀ N₀ < A.card := by
      by_contra hn
      have hpow : 2 ^ A.card ≤ 2 ^ max n₀ N₀ :=
        pow_le_pow_right₀ (by omega) (by omega)
      have hmul : 2 ^ max n₀ N₀ ≤ (K + 2 ^ max n₀ N₀) * N := by
        calc
          _ ≤ K + 2 ^ max n₀ N₀ := Nat.le_add_left _ _
          _ ≤ (K + 2 ^ max n₀ N₀) * N := by
            simpa using Nat.mul_le_mul_left (K + 2 ^ max n₀ N₀) hpos
      omega
    have hcard : A.card ≤ N := by
      simpa using Finset.card_le_card hA.1
    refine ⟨N, A, hA, hN, lt_of_le_of_lt (le_max_left _ _) hlarge,
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hlarge) hcard, ?_⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_right N (Nat.le_add_right _ _)) hlt
  · intro h K
    obtain ⟨N, A, hA, hN, _, _, hlt⟩ := h K 0 0
    exact ⟨N, A, hA, hN, hlt⟩

/-- A uniform estimate for all sufficiently large cardinalities suffices. -/
theorem uniform_bound_eventually_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ K n₀ : ℕ, ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → n₀ ≤ A.card → 2 ^ A.card ≤ K * N) := by
  rw [uniform_bound_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, 0, fun N A hA hN _ => hK N A hA hN⟩
  · rintro ⟨K, n₀, h⟩
    refine ⟨K + 2 ^ n₀, fun N A hA hN => ?_⟩
    by_cases hn : n₀ ≤ A.card
    · exact (h N A hA hN hn).trans
        (Nat.mul_le_mul_right N (Nat.le_add_right _ _))
    · calc
        2 ^ A.card ≤ 2 ^ n₀ := pow_le_pow_right₀ (by omega) (by omega)
        _ ≤ K + 2 ^ n₀ := Nat.le_add_left _ _
        _ ≤ (K + 2 ^ n₀) * N := by
          simpa using Nat.mul_le_mul_left (K + 2 ^ n₀) (Nat.one_le_iff_ne_zero.mpr hN)


namespace ParityReduction

abbrev SumInjective (A : Finset ℕ) : Prop :=
  (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

lemma sums_eq_iff {A : Finset ℕ} (h : SumInjective A)
    {S T : Finset ℕ} (hS : S ⊆ A) (hT : T ⊆ A) :
    S.sum id = T.sum id ↔ S = T := by
  constructor
  · intro he
    exact congrArg Subtype.val (@h ⟨S, Finset.mem_powerset.mpr hS⟩
      ⟨T, Finset.mem_powerset.mpr hT⟩ he)
  · rintro rfl
    rfl

lemma mono {A C : Finset ℕ} (h : SumInjective A) (hC : C ⊆ A) :
    SumInjective C := by
  intro S T he
  apply Subtype.ext
  exact (sums_eq_iff h ((Finset.mem_powerset.mp S.property).trans hC)
    ((Finset.mem_powerset.mp T.property).trans hC)).mp he

lemma insert_of_no_cross {C : Finset ℕ} {d : ℕ} (hC : SumInjective C)
    (hcross : ∀ S ⊆ C, ∀ T ⊆ C, S.sum id ≠ d + T.sum id) :
    SumInjective (insert d C) := by
  intro S T he
  apply Subtype.ext
  change S.val.sum id = T.val.sum id at he
  have hS := Finset.mem_powerset.mp S.property
  have hT := Finset.mem_powerset.mp T.property
  by_cases hdS : d ∈ S.val
  · by_cases hdT : d ∈ T.val
    · have hS' : S.val.erase d ⊆ C := by
        intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hxd, hx⟩
        exact (Finset.mem_insert.mp (hS hx)).resolve_left hxd
      have hT' : T.val.erase d ⊆ C := by
        intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hxd, hx⟩
        exact (Finset.mem_insert.mp (hT hx)).resolve_left hxd
      have he' : (S.val.erase d).sum id = (T.val.erase d).sum id := by
        have hs := Finset.sum_erase_add S.val id hdS
        have ht := Finset.sum_erase_add T.val id hdT
        simp only [id_eq] at hs ht he ⊢
        omega
      have hST := (sums_eq_iff hC hS' hT').mp he'
      simpa only [Finset.insert_erase hdS, Finset.insert_erase hdT] using
        congrArg (insert d) hST
    · have hS' : S.val.erase d ⊆ C := by
        intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hxd, hx⟩
        exact (Finset.mem_insert.mp (hS hx)).resolve_left hxd
      have hT' : T.val ⊆ C := (Finset.subset_insert_iff_of_notMem hdT).mp hT
      exfalso
      apply hcross T.val hT' (S.val.erase d) hS'
      have hs := Finset.sum_erase_add S.val id hdS
      simp only [id_eq] at hs he ⊢
      omega
  · have hS' : S.val ⊆ C := (Finset.subset_insert_iff_of_notMem hdS).mp hS
    by_cases hdT : d ∈ T.val
    · have hT' : T.val.erase d ⊆ C := by
        intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hxd, hx⟩
        exact (Finset.mem_insert.mp (hT hx)).resolve_left hxd
      exfalso
      apply hcross S.val hS' (T.val.erase d) hT'
      have ht := Finset.sum_erase_add T.val id hdT
      simp only [id_eq] at ht he ⊢
      omega
    · have hT' : T.val ⊆ C := (Finset.subset_insert_iff_of_notMem hdT).mp hT
      exact (sums_eq_iff hC hS' hT').mp he

/-- Two entries may be contracted to their positive difference. -/
theorem contract {A C : Finset ℕ} {a b : ℕ} (hA : SumInjective A)
    (hC : C ⊆ A) (ha : a ∈ A) (hb : b ∈ A)
    (haC : a ∉ C) (hbC : b ∉ C) (hab : a < b) :
    SumInjective (insert (b - a) C) := by
  apply insert_of_no_cross (mono hA hC)
  intro S hS T hT he
  have haS : a ∉ S := fun hm => haC (hS hm)
  have hbT : b ∉ T := fun hm => hbC (hT hm)
  have he' : (insert a S).sum id = (insert b T).sum id := by
    rw [Finset.sum_insert haS, Finset.sum_insert hbT]
    simp only [id_eq] at he ⊢
    omega
  have heq := (sums_eq_iff hA (Finset.insert_subset ha (hS.trans hC))
    (Finset.insert_subset hb (hT.trans hC))).mp he'
  have hbS : b ∈ insert a S := heq.symm ▸ Finset.mem_insert_self b T
  rcases Finset.mem_insert.mp hbS with hba | hbS
  · omega
  · exact hbC (hS hbS)

lemma difference_not_mem {A C : Finset ℕ} {a b : ℕ} (hA : SumInjective A)
    (hC : C ⊆ A) (ha : a ∈ A) (hb : b ∈ A)
    (haC : a ∉ C) (hab : a < b) : b - a ∉ C := by
  intro hd
  have had : a ≠ b - a := fun he => haC (he.symm ▸ hd)
  have he : ({b} : Finset ℕ).sum id = ({a, b - a} : Finset ℕ).sum id := by
    have ha' : a ∉ ({b - a} : Finset ℕ) := by simpa using had
    rw [Finset.sum_insert ha']
    simp only [Finset.sum_singleton, id_eq]
    omega
  have heq := (sums_eq_iff hA (Finset.singleton_subset_iff.mpr hb)
    (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr (hC hd)))).mp he
  have ha' : a ∈ ({b} : Finset ℕ) := heq.symm ▸ Finset.mem_insert_self a {b - a}
  simp only [Finset.mem_singleton] at ha'
  omega


lemma unscale {B : Finset ℕ} (h : SumInjective (B.image (fun x => 2 * x))) :
    SumInjective B := by
  have hinj : Function.Injective (fun x : ℕ => 2 * x) :=
    fun _ _ he => Nat.mul_left_cancel (by omega) he
  intro S T he
  apply Subtype.ext
  apply Finset.image_injective hinj
  apply (sums_eq_iff h
    (Finset.image_subset_image (Finset.mem_powerset.mp S.property))
    (Finset.image_subset_image (Finset.mem_powerset.mp T.property))).mp
  rw [Finset.sum_image (fun _ _ _ _ he => hinj he),
    Finset.sum_image (fun _ _ _ _ he => hinj he)]
  simp only [id_eq]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change S.val.sum id = T.val.sum id at he
  simpa only [id_eq] using congrArg (2 * ·) he

/-- Halving an all-even set preserves its cardinality and distinct subset sums. -/
theorem halve {D : Finset ℕ} {N : ℕ} (hD : SumInjective D)
    (hbound : D ⊆ Finset.Icc 1 N) (heven : ∀ x ∈ D, 2 ∣ x) :
    SumInjective (D.image (fun x => x / 2)) ∧
    (D.image (fun x => x / 2)).card = D.card ∧
    D.image (fun x => x / 2) ⊆ Finset.Icc 1 (N / 2) := by
  have hback : (D.image (fun x => x / 2)).image (fun x => 2 * x) = D := by
    rw [Finset.image_image]
    calc
      D.image (fun x => 2 * (x / 2)) = D.image id :=
        Finset.image_congr (fun x hx => Nat.mul_div_cancel' (heven x hx))
      _ = D := Finset.image_id
  refine ⟨unscale (hback.symm ▸ hD), ?_, ?_⟩
  · apply Finset.card_image_of_injOn
    intro x hx y hy he
    have hx' := Nat.mul_div_cancel' (heven x hx)
    have hy' := Nat.mul_div_cancel' (heven y hy)
    change x / 2 = y / 2 at he
    omega
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyb := Finset.mem_Icc.mp (hbound hy)
    have hy' := Nat.mul_div_cancel' (heven y hy)
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hyb.2⟩

/-- When precisely two entries are odd, one can remove one bit and halve the bound. -/
theorem reduce_two_odd {A : Finset ℕ} {N a b : ℕ} (hA : SumInjective A)
    (hbound : A ⊆ Finset.Icc 1 N) (ha : a ∈ A) (hb : b ∈ A) (hab : a < b)
    (hodd : ∀ x ∈ A, x % 2 = 1 ↔ x = a ∨ x = b) :
    ∃ B : Finset ℕ, SumInjective B ∧ B ⊆ Finset.Icc 1 (N / 2) ∧
      B.card + 1 = A.card := by
  let C := (A.erase a).erase b
  have hC : C ⊆ A := (Finset.erase_subset b _).trans (Finset.erase_subset a A)
  have haC : a ∉ C := by simp [C]
  have hbC : b ∉ C := by simp [C]
  have hb' : b ∈ A.erase a := Finset.mem_erase.mpr ⟨by omega, hb⟩
  have hCcard : C.card + 2 = A.card := by
    simp only [C, Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    have hpos := Finset.card_pos.mpr ⟨b, hb'⟩
    rw [Finset.card_erase_of_mem ha] at hpos
    omega
  let D := insert (b - a) C
  have hD : SumInjective D := contract hA hC ha hb haC hbC hab
  have hDcard : D.card + 1 = A.card := by
    rw [show D = insert (b - a) C from rfl,
      Finset.card_insert_of_notMem (difference_not_mem hA hC ha hb haC hab)]
    omega
  have hDbound : D ⊆ Finset.Icc 1 N := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have hbN := (Finset.mem_Icc.mp (hbound hb)).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · exact hbound (hC hx)
  have hDeven : ∀ x ∈ D, 2 ∣ x := by
    intro x hx
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have haodd := (hodd a ha).mpr (Or.inl rfl)
      have hbodd := (hodd b hb).mpr (Or.inr rfl)
      omega
    · have hxa : x ≠ a := fun he => haC (he ▸ hx)
      have hxb : x ≠ b := fun he => hbC (he ▸ hx)
      have hxodd := hodd x (hC hx)
      omega
  obtain ⟨hB, hBcard, hBbound⟩ := halve hD hDbound hDeven
  exact ⟨D.image (fun x => x / 2), hB, hBbound, by omega⟩


/-- The two-odd-entry contraction preserves a violation of any integer uniform bound. -/
theorem reduce_two_odd_counterexample {A : Finset ℕ} {N a b K : ℕ}
    (hA : SumInjective A) (hbound : A ⊆ Finset.Icc 1 N)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a < b)
    (hodd : ∀ x ∈ A, x % 2 = 1 ↔ x = a ∨ x = b)
    (hlt : K * N < 2 ^ A.card) :
    ∃ B : Finset ℕ, SumInjective B ∧ B ⊆ Finset.Icc 1 (N / 2) ∧
      N / 2 ≠ 0 ∧ N / 2 < N ∧ K * (N / 2) < 2 ^ B.card := by
  obtain ⟨B, hB, hBbound, hBcard⟩ := reduce_two_odd hA hbound ha hb hab hodd
  have ha1 := (Finset.mem_Icc.mp (hbound ha)).1
  have hbN := (Finset.mem_Icc.mp (hbound hb)).2
  refine ⟨B, hB, hBbound, by omega, by omega, ?_⟩
  have hhalf : 2 * (N / 2) ≤ N := by omega
  have hmul := Nat.mul_le_mul_left K hhalf
  have hpow : 2 ^ A.card = 2 * 2 ^ B.card := by rw [← hBcard, pow_succ]; omega
  rw [hpow] at hlt
  nlinarith

/-- With one odd entry, delete that entry and halve the others. -/
theorem reduce_one_odd {A : Finset ℕ} {N a : ℕ} (hA : SumInjective A)
    (hbound : A ⊆ Finset.Icc 1 N) (ha : a ∈ A)
    (hodd : ∀ x ∈ A, x % 2 = 1 ↔ x = a) :
    ∃ B : Finset ℕ, SumInjective B ∧ B ⊆ Finset.Icc 1 (N / 2) ∧
      B.card + 1 = A.card := by
  have hC : SumInjective (A.erase a) := mono hA (Finset.erase_subset a A)
  have hCbound : A.erase a ⊆ Finset.Icc 1 N := (Finset.erase_subset a A).trans hbound
  have hCeven : ∀ x ∈ A.erase a, 2 ∣ x := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxa, hx⟩
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hxodd := hodd x hx
    omega
  obtain ⟨hB, hBcard, hBbound⟩ := halve hC hCbound hCeven
  refine ⟨(A.erase a).image (fun x => x / 2), hB, hBbound, ?_⟩
  rw [hBcard, Finset.card_erase_of_mem ha]
  have hpos := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- At most two odd entries permit halving while losing at most one entry. -/
theorem reduce_few_odd {A : Finset ℕ} {N : ℕ} (hA : SumInjective A)
    (hbound : A ⊆ Finset.Icc 1 N)
    (hcard : (A.filter (fun x => x % 2 = 1)).card ≤ 2) :
    ∃ B : Finset ℕ, SumInjective B ∧ B ⊆ Finset.Icc 1 (N / 2) ∧
      A.card ≤ B.card + 1 := by
  let O := A.filter (fun x => x % 2 = 1)
  by_cases hO : O.Nonempty
  · obtain ⟨a, haO⟩ := hO
    have ha : a ∈ A := (Finset.mem_filter.mp haO).1
    by_cases hsecond : ∃ b ∈ O, b ≠ a
    · obtain ⟨b, hbO, hba⟩ := hsecond
      have hb : b ∈ A := (Finset.mem_filter.mp hbO).1
      have habO : ({a, b} : Finset ℕ) ⊆ O :=
        Finset.insert_subset haO (Finset.singleton_subset_iff.mpr hbO)
      have hEq : ({a, b} : Finset ℕ) = O :=
        Finset.eq_of_subset_of_card_le habO (by simpa [Ne.symm hba] using hcard)
      have hodd : ∀ x ∈ A, x % 2 = 1 ↔ x = a ∨ x = b := by
        intro x hx
        have hm : x % 2 = 1 ↔ x ∈ O := by simp [O, hx]
        rw [hm, ← hEq]
        simp
      obtain hab | hab := lt_or_gt_of_ne (Ne.symm hba)
      · obtain ⟨B, hB, hBbound, hBcard⟩ := reduce_two_odd hA hbound ha hb hab hodd
        exact ⟨B, hB, hBbound, hBcard.ge⟩
      · have hodd' : ∀ x ∈ A, x % 2 = 1 ↔ x = b ∨ x = a := by
          intro x hx
          exact (hodd x hx).trans or_comm
        obtain ⟨B, hB, hBbound, hBcard⟩ := reduce_two_odd hA hbound hb ha hab hodd'
        exact ⟨B, hB, hBbound, hBcard.ge⟩
    · have hodd : ∀ x ∈ A, x % 2 = 1 ↔ x = a := by
        intro x hx
        constructor
        · intro ho
          by_contra hne
          exact hsecond ⟨x, Finset.mem_filter.mpr ⟨hx, ho⟩, hne⟩
        · rintro rfl
          exact (Finset.mem_filter.mp haO).2
      obtain ⟨B, hB, hBbound, hBcard⟩ := reduce_one_odd hA hbound ha hodd
      exact ⟨B, hB, hBbound, hBcard.ge⟩
  · have heven : ∀ x ∈ A, 2 ∣ x := by
      intro x hx
      apply Nat.dvd_iff_mod_eq_zero.mpr
      have hnot : x % 2 ≠ 1 := fun ho => hO ⟨x, Finset.mem_filter.mpr ⟨hx, ho⟩⟩
      omega
    obtain ⟨hB, hBcard, hBbound⟩ := halve hA hbound heven
    exact ⟨A.image (fun x => x / 2), hB, hBbound, by omega⟩


/-- It suffices to establish a uniform bound for sets with at least three odd entries. -/
theorem uniform_from_three_odd {K : ℕ}
    (h : ∀ (N : ℕ) (A : Finset ℕ), SumInjective A → A ⊆ Finset.Icc 1 N → N ≠ 0 →
      3 ≤ (A.filter (fun x => x % 2 = 1)).card → 2 ^ A.card ≤ K * N) :
    ∀ (N : ℕ) (A : Finset ℕ), SumInjective A → A ⊆ Finset.Icc 1 N → N ≠ 0 →
      2 ^ A.card ≤ max K 2 * N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro A hA hbound hN
    by_cases hN2 : 2 ≤ N
    · by_cases hodd : 3 ≤ (A.filter (fun x => x % 2 = 1)).card
      · exact (h N A hA hbound hN hodd).trans
          (Nat.mul_le_mul_right N (le_max_left _ _))
      · obtain ⟨B, hB, hBbound, hcard⟩ := reduce_few_odd hA hbound (by omega)
        have hBpow := ih (N / 2) (by omega) B hB hBbound (by omega)
        have hpow : 2 ^ A.card ≤ 2 * 2 ^ B.card := by
          calc
            _ ≤ 2 ^ (B.card + 1) := pow_le_pow_right₀ (by omega) hcard
            _ = _ := by rw [pow_succ]; omega
        have hhalf : 2 * (N / 2) ≤ N := by omega
        have hmul := Nat.mul_le_mul_left (max K 2) hhalf
        nlinarith
    · have hN1 : N = 1 := by omega
      have hcard : A.card ≤ 1 := by
        simpa [hN1] using Finset.card_le_card hbound
      have hpow : 2 ^ A.card ≤ 2 := by
        simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by omega) hcard
      simpa [hN1] using hpow.trans (le_max_right K 2)

/-- Doubling preserves distinct subset sums. -/
lemma double_sum_injective {A : Finset ℕ} (hA : SumInjective A) :
    SumInjective (A.image (fun x => 2 * x)) := by
  have hinj : Function.Injective (fun x : ℕ => 2 * x) :=
    fun _ _ he => Nat.mul_left_cancel (by omega) he
  intro S T he
  obtain ⟨s, hs, hsi⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp S.property)
  obtain ⟨t, ht, hti⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp T.property)
  apply Subtype.ext
  change S.val.sum id = T.val.sum id at he
  rw [← hsi, ← hti, Finset.sum_image hinj.injOn, Finset.sum_image hinj.injOn] at he
  simp only [id_eq] at he
  rw [← Finset.mul_sum, ← Finset.mul_sum] at he
  have hst : s = t := (sums_eq_iff hA hs ht).mp (Nat.mul_left_cancel (by omega) he)
  rw [← hsi, ← hti, hst]

/-- Add a new low binary digit to a sum-distinct set. -/
def binaryExtension (A : Finset ℕ) : Finset ℕ := insert 1 (A.image (fun x => 2 * x))

lemma binaryExtension_sum_injective {A : Finset ℕ} (hA : SumInjective A) :
    SumInjective (binaryExtension A) := by
  apply insert_of_no_cross (double_sum_injective hA)
  have heven (S : Finset ℕ) (hS : S ⊆ A.image (fun x => 2 * x)) : 2 ∣ S.sum id := by
    apply Finset.dvd_sum
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact dvd_mul_right 2 a
  intro S hS T hT he
  have hs := Nat.dvd_iff_mod_eq_zero.mp (heven S hS)
  have ht := Nat.dvd_iff_mod_eq_zero.mp (heven T hT)
  omega

lemma binaryExtension_card (A : Finset ℕ) : (binaryExtension A).card = A.card + 1 := by
  have hnot : 1 ∉ A.image (fun x => 2 * x) := by
    intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    omega
  rw [binaryExtension, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (fun _ _ he => Nat.mul_left_cancel (by omega) he)]

lemma binaryExtension_bound {A : Finset ℕ} {N : ℕ}
    (hbound : A ⊆ Finset.Icc 1 N) (hN : N ≠ 0) :
    binaryExtension A ⊆ Finset.Icc 1 (2 * N) := by
  apply Finset.insert_subset
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hb := Finset.mem_Icc.mp (hbound ha)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

def binaryExtensionIter : ℕ → Finset ℕ → Finset ℕ
  | 0, A => A
  | k + 1, A => binaryExtension (binaryExtensionIter k A)

lemma binaryExtensionIter_sum_injective {A : Finset ℕ} (hA : SumInjective A) (k : ℕ) :
    SumInjective (binaryExtensionIter k A) := by
  induction k with
  | zero => exact hA
  | succ k ih => exact binaryExtension_sum_injective ih

lemma binaryExtensionIter_card (A : Finset ℕ) (k : ℕ) :
    (binaryExtensionIter k A).card = A.card + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [binaryExtensionIter, binaryExtension_card, ih, Nat.add_assoc]

lemma binaryExtensionIter_bound {A : Finset ℕ} {N : ℕ}
    (hbound : A ⊆ Finset.Icc 1 N) (hN : N ≠ 0) (k : ℕ) :
    binaryExtensionIter k A ⊆ Finset.Icc 1 (2 ^ k * N) := by
  induction k with
  | zero => simpa [binaryExtensionIter] using hbound
  | succ k ih =>
    have hb := binaryExtension_bound ih (Nat.mul_ne_zero (by positivity) hN)
    simpa [binaryExtensionIter, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb

/-- A single constant valid on an unbounded collection of cardinalities suffices. -/
theorem uniform_from_unbounded_cardinalities {K : ℕ}
    (h : ∀ n₀ : ℕ, ∃ m ≥ n₀, ∀ (N : ℕ) (A : Finset ℕ),
      SumInjective A → A ⊆ Finset.Icc 1 N → N ≠ 0 → A.card = m →
      2 ^ A.card ≤ K * N) :
    ∀ (N : ℕ) (A : Finset ℕ), SumInjective A → A ⊆ Finset.Icc 1 N → N ≠ 0 →
      2 ^ A.card ≤ K * N := by
  intro N A hA hbound hN
  obtain ⟨m, hm, hgood⟩ := h A.card
  let k := m - A.card
  have hcard : (binaryExtensionIter k A).card = m := by
    rw [binaryExtensionIter_card]
    dsimp [k]
    omega
  have hpow := hgood (2 ^ k * N) (binaryExtensionIter k A)
    (binaryExtensionIter_sum_injective hA k) (binaryExtensionIter_bound hbound hN k)
    (Nat.mul_ne_zero (by positivity) hN) hcard
  rw [binaryExtensionIter_card, pow_add] at hpow
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ k) _ (by positivity)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow


end ParityReduction

/-- It suffices to prove the conjectured bound for sets with at least three odd entries. -/
theorem uniform_bound_three_odd_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → 3 ≤ (A.filter (fun x => x % 2 = 1)).card →
      2 ^ A.card ≤ K * N) := by
  rw [uniform_bound_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun N A hA hN _ => hK N A hA hN⟩
  · rintro ⟨K, hK⟩
    refine ⟨max K 2, fun N A hA hN => ?_⟩
    exact ParityReduction.uniform_from_three_odd
      (fun M B hsum hbound hM hodd => hK M B ⟨hbound, hsum⟩ hM hodd)
      N A hA.2 hA.1 hN

/-- A single bound on an unbounded collection of cardinalities is sufficient. -/
theorem uniform_bound_unbounded_cardinalities_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ K : ℕ, ∀ n₀ : ℕ, ∃ m ≥ n₀, ∀ (N : ℕ) (A : Finset ℕ),
      IsSumDistinctSet A N → N ≠ 0 → A.card = m → 2 ^ A.card ≤ K * N) := by
  rw [uniform_bound_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun n₀ => ⟨n₀, le_rfl, fun N A hA hN _ => hK N A hA hN⟩⟩
  · rintro ⟨K, hK⟩
    refine ⟨K, fun N A hA hN => ?_⟩
    apply ParityReduction.uniform_from_unbounded_cardinalities (K := K) ?_ N A hA.2 hA.1 hN
    intro n₀
    obtain ⟨m, hm, hgood⟩ := hK n₀
    exact ⟨m, hm, fun M B hsum hbound hM hcard =>
      hgood M B ⟨hbound, hsum⟩ hM hcard⟩

/-- Failure would supply counterexamples at every sufficiently large cardinality. -/
theorem negation_eventually_all_cardinalities_iff :
    (¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∀ K : ℕ, ∃ n₀ : ℕ, ∀ m ≥ n₀, ∃ (N : ℕ) (A : Finset ℕ),
      IsSumDistinctSet A N ∧ N ≠ 0 ∧ A.card = m ∧ K * N < 2 ^ A.card) := by
  rw [uniform_bound_unbounded_cardinalities_iff]
  push_neg
  rfl

namespace DigitReduction

abbrev SumInjective (A : Finset ℕ) : Prop :=
  (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

/-- All digit vectors with entries less than `q` have different weighted sums. -/
def DigitInjective {k : ℕ} (a : Fin k → ℕ) (q : ℕ) : Prop :=
  Function.Injective (fun d : Fin k → Fin q => ∑ i, (d i : ℕ) * a i)

private def row {k m : ℕ} (S : Finset (Fin k × Fin m)) (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter (fun j => (i, j) ∈ S)

private lemma binary_sum_lt {m : ℕ} (s : Finset (Fin m)) :
    ∑ j ∈ s, 2 ^ j.val < 2 ^ m := by
  have hle : ∑ j ∈ s, 2 ^ j.val ≤ ∑ j : Fin m, 2 ^ j.val :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  rw [Fin.sum_univ_eq_sum_range] at hle
  have hgeom := geom_sum_mul_add (R := ℕ) 1 m
  simp only [Nat.reduceAdd, mul_one] at hgeom
  omega

private def digits {k m : ℕ} (S : Finset (Fin k × Fin m)) : Fin k → Fin (2 ^ m) :=
  fun i => ⟨∑ j ∈ row S i, 2 ^ j.val, binary_sum_lt _⟩

private lemma digits_injective {k m : ℕ} :
    Function.Injective (@digits k m) := by
  intro S T h
  have hrow (i : Fin k) : row S i = row T i := by
    have hi := congrArg (fun d : Fin k → Fin (2 ^ m) => (d i).val) h
    change (∑ j ∈ row S i, 2 ^ j.val) = ∑ j ∈ row T i, 2 ^ j.val at hi
    have him : (row S i).image Fin.val = (row T i).image Fin.val := by
      apply Finset.geomSum_injective (by omega : 2 ≤ (2 : ℕ))
      simpa only [Finset.sum_image Fin.val_injective.injOn] using hi
    exact Finset.image_injective Fin.val_injective him
  ext p
  simpa only [row, Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.ext_iff.mp (hrow p.1) p.2)

private lemma sum_eq_digits {k m : ℕ} (a : Fin k → ℕ) (S : Finset (Fin k × Fin m)) :
    ∑ p ∈ S, 2 ^ p.2.val * a p.1 = ∑ i, ((digits S i : Fin (2 ^ m)) : ℕ) * a i := by
  simp only [digits, row, Finset.sum_mul, Finset.sum_filter]
  simp_rw [ite_mul, zero_mul]
  rw [← Fintype.sum_prod_type (fun p : Fin k × Fin m =>
    if p ∈ S then 2 ^ p.2.val * a p.1 else 0)]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

/-- Digit injectivity implies injectivity of all subset sums of the indexed binary expansion. -/
lemma indexed_sum_injective {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) :
    Function.Injective (fun S : Finset (Fin k × Fin m) =>
      ∑ p ∈ S, 2 ^ p.2.val * a p.1) := by
  intro S T hST
  apply digits_injective
  apply h
  simpa only [← sum_eq_digits] using hST

lemma weight_injective {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) :
    Function.Injective (fun p : Fin k × Fin m => 2 ^ p.2.val * a p.1) := by
  intro p q hpq
  apply Finset.singleton_injective
  apply indexed_sum_injective h
  simpa only [Finset.sum_singleton] using hpq

lemma weight_pos {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) (p : Fin k × Fin m) :
    0 < 2 ^ p.2.val * a p.1 := by
  by_contra hp
  have hz : 2 ^ p.2.val * a p.1 = 0 := by omega
  have he : ({p} : Finset (Fin k × Fin m)) = ∅ :=
    indexed_sum_injective h (by simpa only [Finset.sum_singleton, Finset.sum_empty] using hz)
  exact Finset.singleton_ne_empty p he

/-- Expand each coefficient into `m` binary places. -/
def binaryBlock {k : ℕ} (a : Fin k → ℕ) (m : ℕ) : Finset ℕ :=
  Finset.univ.image (fun p : Fin k × Fin m => 2 ^ p.2.val * a p.1)

lemma binaryBlock_card {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) :
    (binaryBlock a m).card = k * m := by
  rw [binaryBlock, Finset.card_image_of_injective _ (weight_injective h)]
  simp

lemma binaryBlock_sum_injective {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) : SumInjective (binaryBlock a m) := by
  intro S T hST
  obtain ⟨s, _, hs⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp S.property)
  obtain ⟨t, _, ht⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp T.property)
  apply Subtype.ext
  change S.val = T.val
  change S.val.sum id = T.val.sum id at hST
  rw [← hs, ← ht, Finset.sum_image (weight_injective h).injOn,
    Finset.sum_image (weight_injective h).injOn] at hST
  have heq : s = t := indexed_sum_injective h hST
  rw [← hs, ← ht, heq]

lemma binaryBlock_bound {k m M : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) (hM : ∀ i, a i ≤ M) :
    binaryBlock a m ⊆ Finset.Icc 1 (2 ^ (m - 1) * M) := by
  intro x hx
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_Icc.mpr ⟨weight_pos h p, ?_⟩
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega)) (hM p.1)

/-- Exact second moment of the binary expansion, before any use of a lower bound. -/
lemma binaryBlock_sum_sq {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) :
    3 * (∑ b ∈ binaryBlock a m, (b : ℝ) ^ 2) =
      ((4 : ℝ) ^ m - 1) * ∑ i, (a i : ℝ) ^ 2 := by
  have hp (j : ℕ) : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hg : (∑ j : Fin m, (4 : ℝ) ^ j.val) * 3 = 4 ^ m - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    convert geom_sum_mul (4 : ℝ) m using 1
    norm_num
  rw [binaryBlock, Finset.sum_image (weight_injective h).injOn]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, hp]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [← hg]
  ring

/-- The second-moment lower bound expressed directly in terms of digit coefficients. -/
lemma digit_second_moment_bound {k m : ℕ} {a : Fin k → ℕ}
    (h : DigitInjective a (2 ^ m)) :
    (((2 : ℝ) ^ m) ^ k) ^ 2 ≤
      ((4 : ℝ) ^ m - 1) * (∑ i, (a i : ℝ) ^ 2) + 1 := by
  have hb := sum_sq_bound (binaryBlock a m) (binaryBlock_sum_injective h)
  rw [binaryBlock_card h, binaryBlock_sum_sq h, Nat.mul_comm k m, pow_mul] at hb
  exact hb

/-- Normalizing removes the digit base, but still loses the square root of the
number of coefficient directions. -/
lemma digit_normalized_bound {k m M : ℕ} {a : Fin k → ℕ}
    (hk : 0 < k) (hM : M ≠ 0) (h : DigitInjective a (2 ^ m))
    (hbound : ∀ i, a i ≤ M) :
    (((2 : ℝ) ^ m) ^ (k - 1)) ^ 2 ≤ (k : ℝ) * (M : ℝ) ^ 2 := by
  have hb := digit_second_moment_bound h
  have hs : (∑ i, (a i : ℝ) ^ 2) ≤ (k : ℝ) * (M : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin k, (M : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
        exact_mod_cast hbound i
      _ = _ := by simp
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hMR : 1 ≤ (M : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM
  have hu : 1 ≤ (k : ℝ) * (M : ℝ) ^ 2 := by
    have hsq : 1 ≤ (M : ℝ) ^ 2 := by nlinarith
    nlinarith
  have h4 : 1 ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hp : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have he : (((2 : ℝ) ^ m) ^ k) ^ 2 =
      (4 : ℝ) ^ m * (((2 : ℝ) ^ m) ^ (k - 1)) ^ 2 := by
    calc
      _ = (((2 : ℝ) ^ m) * ((2 : ℝ) ^ m) ^ (k - 1)) ^ 2 := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = _ := by rw [mul_pow, hp]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < (4 : ℝ) ^ m)).mp
  calc
    (4 : ℝ) ^ m * (((2 : ℝ) ^ m) ^ (k - 1)) ^ 2 =
        (((2 : ℝ) ^ m) ^ k) ^ 2 := he.symm
    _ ≤ ((4 : ℝ) ^ m - 1) * (∑ i, (a i : ℝ) ^ 2) + 1 := hb
    _ ≤ ((4 : ℝ) ^ m - 1) * ((k : ℝ) * (M : ℝ) ^ 2) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr h4)) le_rfl
    _ ≤ (4 : ℝ) ^ m * ((k : ℝ) * (M : ℝ) ^ 2) := by nlinarith only [hu]

/-- Any digit example beating a factor `K` must have more than `K²` directions. -/
lemma dimension_lower_bound_for_digit_examples {k m M K : ℕ} {a : Fin k → ℕ}
    (hk : 0 < k) (hM : M ≠ 0) (h : DigitInjective a (2 ^ m))
    (hbound : ∀ i, a i ≤ M) (hbad : K * M < (2 ^ m) ^ (k - 1)) : K ^ 2 < k := by
  have hb : ((2 ^ m) ^ (k - 1)) ^ 2 ≤ k * M ^ 2 := by
    exact_mod_cast digit_normalized_bound hk hM h hbound
  have hl : (K * M) ^ 2 < ((2 ^ m) ^ (k - 1)) ^ 2 :=
    (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mpr hbad
  rw [mul_pow] at hl
  exact Nat.lt_of_mul_lt_mul_right (hl.trans_le hb)

/-- A sufficient condition for a disproof. The digit examples required by the
hypothesis have NOT been constructed. -/
theorem negation_of_digit_examples
    (h : ∀ K : ℕ, ∃ (k m M : ℕ) (a : Fin k → ℕ),
      0 < k ∧ 0 < m ∧ M ≠ 0 ∧ DigitInjective a (2 ^ m) ∧
        (∀ i, a i ≤ M) ∧ K * M < (2 ^ m) ^ (k - 1)) :
    ¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N := by
  rw [negation_iff]
  intro K
  obtain ⟨k, m, M, a, hk, hm, hM, hinj, hbound, hbad⟩ := h K
  refine ⟨2 ^ (m - 1) * M, binaryBlock a m,
    ⟨binaryBlock_bound hinj hbound, binaryBlock_sum_injective hinj⟩,
    Nat.mul_ne_zero (by positivity) hM, ?_⟩
  rw [binaryBlock_card hinj]
  calc
    K * (2 ^ (m - 1) * M) ≤ 2 ^ m * (K * M) := by
      have he := Nat.mul_le_mul_right (K * M)
        (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (Nat.sub_le m 1))
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
    _ < 2 ^ m * (2 ^ m) ^ (k - 1) :=
      Nat.mul_lt_mul_of_pos_left hbad (by positivity)
    _ = 2 ^ (k * m) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k), ← pow_mul, Nat.mul_comm]

end DigitReduction

namespace LocalReduction

/-- Each generator is the first missing positive difference of subset sums of
all the other generators. The missing-difference assertion at the generator
itself follows separately from subset-sum injectivity. -/
def LocallyMinimal (A : Finset ℕ) : Prop :=
  ∀ b ∈ A, ∀ c : ℕ, 0 < c → c < b →
    ∃ S ⊆ A.erase b, ∃ T ⊆ A.erase b, S.sum id = c + T.sum id

lemma locallyMinimal_of_sum_minimal {N : ℕ} {A : Finset ℕ}
    (hA : IsSumDistinctSet A N)
    (hmin : ∀ B : Finset ℕ, IsSumDistinctSet B N → B.card = A.card →
      A.sum id ≤ B.sum id) : LocallyMinimal A := by
  intro b hb c hc hcb
  by_contra hno
  push_neg at hno
  have hcnot : c ∉ A.erase b := by
    intro hcA
    have hh := hno {c} (Finset.singleton_subset_iff.mpr hcA) ∅ (Finset.empty_subset _)
    simp at hh
  let B := insert c (A.erase b)
  have hB : IsSumDistinctSet B N := by
    constructor
    · apply Finset.insert_subset
      · exact Finset.mem_Icc.mpr ⟨hc, le_trans hcb.le (Finset.mem_Icc.mp (hA.1 hb)).2⟩
      · exact (Finset.erase_subset _ _).trans hA.1
    · exact ParityReduction.insert_of_no_cross
        (ParityReduction.mono hA.2 (Finset.erase_subset _ _)) hno
  have hcard : B.card = A.card := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hcnot, Finset.card_erase_of_mem hb]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  have hle := hmin B hB hcard
  have hsum := Finset.sum_erase_add A id hb
  dsimp [B] at hle
  rw [Finset.sum_insert hcnot] at hle
  simp only [id_eq] at hle hsum
  omega

/-- Minimize the total sum while preserving both cardinality and ambient bound. -/
theorem exists_sum_minimal {N : ℕ} {A : Finset ℕ} (hA : IsSumDistinctSet A N) :
    ∃ B : Finset ℕ, IsSumDistinctSet B N ∧ B.card = A.card ∧
      (∀ C : Finset ℕ, IsSumDistinctSet C N → C.card = B.card → B.sum id ≤ C.sum id) := by
  classical
  let candidates := (Finset.Icc 1 N).powerset.filter
    (fun B => B.card = A.card ∧ IsSumDistinctSet B N)
  have hmem (B : Finset ℕ) : B ∈ candidates ↔
      IsSumDistinctSet B N ∧ B.card = A.card := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, hcard, hB⟩
      exact ⟨hB, hcard⟩
    · rintro ⟨hB, hcard⟩
      exact ⟨hB.1, hcard, hB⟩
  obtain ⟨B, hB, hmin⟩ := candidates.exists_min_image (fun B => B.sum id)
    ⟨A, (hmem A).mpr ⟨hA, rfl⟩⟩
  obtain ⟨hBN, hcard⟩ := (hmem B).mp hB
  refine ⟨B, hBN, hcard, fun C hCN hCcard => ?_⟩
  exact hmin C ((hmem C).mpr ⟨hCN, hCcard.trans hcard⟩)

/-- In particular, the first-missing-difference conditions may be imposed
without changing the cardinality or the ambient bound. -/
theorem exists_locallyMinimal {N : ℕ} {A : Finset ℕ} (hA : IsSumDistinctSet A N) :
    ∃ B : Finset ℕ, IsSumDistinctSet B N ∧ B.card = A.card ∧
      B.sum id ≤ A.sum id ∧ LocallyMinimal B := by
  obtain ⟨B, hB, hcard, hmin⟩ := exists_sum_minimal hA
  exact ⟨B, hB, hcard, hmin A hA hcard.symm, locallyMinimal_of_sum_minimal hB hmin⟩

/-- The generator itself cannot be such a difference. -/
lemma generator_not_difference {A : Finset ℕ} (hA : ParityReduction.SumInjective A)
    {b : ℕ} (hb : b ∈ A) {S T : Finset ℕ} (hS : S ⊆ A.erase b)
    (hT : T ⊆ A.erase b) : S.sum id ≠ b + T.sum id := by
  intro he
  have hbT : b ∉ T := fun hm => Finset.notMem_erase b A (hT hm)
  have he' : S.sum id = (insert b T).sum id := by
    simpa only [Finset.sum_insert hbT, id_eq] using he
  have hST := (ParityReduction.sums_eq_iff hA
    (hS.trans (Finset.erase_subset _ _))
    (Finset.insert_subset hb (hT.trans (Finset.erase_subset _ _)))).mp he'
  have hbS : b ∈ S := hST.symm ▸ Finset.mem_insert_self b T
  exact Finset.notMem_erase b A (hS hbS)

/-- In a locally minimal set, deleting a generator greater than one leaves no
common divisor greater than one. -/
lemma common_divisor_erase_eq_one {A : Finset ℕ} (h : LocallyMinimal A)
    {b d : ℕ} (hb : b ∈ A) (hb1 : 1 < b)
    (hd : ∀ x ∈ A.erase b, d ∣ x) : d = 1 := by
  obtain ⟨S, hS, T, hT, he⟩ := h b hb 1 (by omega) hb1
  have hs : d ∣ S.sum id := Finset.dvd_sum (fun x hx => hd x (hS hx))
  have ht : d ∣ T.sum id := Finset.dvd_sum (fun x hx => hd x (hT hx))
  rw [he] at hs
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_left ht).mpr hs)


/-- If only one generator is nonzero modulo `d`, divisibility of a subset
sum records whether that generator is present. -/
lemma dvd_sum_iff_not_mem {C S : Finset ℕ} {a d : ℕ}
    (hS : S ⊆ C) (ha : ¬ d ∣ a)
    (hdiv : ∀ x ∈ C.erase a, d ∣ x) :
    d ∣ S.sum id ↔ a ∉ S := by
  have hd : d ∣ (S.erase a).sum id := Finset.dvd_sum (fun x hx =>
    hdiv x (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
      hS (Finset.mem_erase.mp hx).2⟩))
  by_cases haS : a ∈ S
  · have he := Finset.sum_erase_add S id haS
    change (S.erase a).sum id + a = S.sum id at he
    rw [← he]
    simpa only [haS, not_true_eq_false, iff_false] using
      (fun h : d ∣ (S.erase a).sum id + a => ha ((Nat.dvd_add_iff_right hd).mpr h))
  · simpa only [Finset.erase_eq_of_notMem haS, haS, not_false_eq_true, iff_true]
      using hd

/-- Two exceptional generators cannot be congruent modulo a common divisor
of all remaining generators in a locally minimal admissible set. -/
theorem no_two_congruent_exceptions {A : Finset ℕ} {a b d : ℕ}
    (hA : ParityReduction.SumInjective A) (hlocal : LocallyMinimal A)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a < b)
    (hda : ¬ d ∣ a) (hdiff : d ∣ b - a)
    (hdiv : ∀ x ∈ (A.erase b).erase a, d ∣ x) : False := by
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun he => hda (he ▸ dvd_zero d))
  obtain ⟨S, hS, T, hT, he⟩ := hlocal b hb (b - a) (by omega) (by omega)
  have hSm := dvd_sum_iff_not_mem hS hda hdiv
  have hTm := dvd_sum_iff_not_mem hT hda hdiv
  have hmem : a ∈ S ↔ a ∈ T := by
    have hdiviff : d ∣ S.sum id ↔ d ∣ T.sum id := by
      rw [he]
      exact (Nat.dvd_add_iff_right hdiff).symm
    tauto
  have he' : (S.erase a).sum id = b - a + (T.erase a).sum id := by
    by_cases haS : a ∈ S
    · have hs := Finset.sum_erase_add S id haS
      have ht := Finset.sum_erase_add T id (hmem.mp haS)
      simp only [id_eq] at hs ht he ⊢
      omega
    · have haT : a ∉ T := fun ht => haS (hmem.mpr ht)
      simpa only [Finset.erase_eq_of_notMem haS, Finset.erase_eq_of_notMem haT] using he
  have haS' : a ∉ S.erase a := Finset.notMem_erase _ _
  have hSa : insert a (S.erase a) ⊆ A.erase b := Finset.insert_subset
    (Finset.mem_erase.mpr ⟨by omega, ha⟩)
    ((Finset.erase_subset _ _).trans hS)
  apply generator_not_difference hA hb hSa ((Finset.erase_subset a T).trans hT)
  rw [Finset.sum_insert haS']
  simp only [id_eq] at he' ⊢
  omega

/-- In particular, a locally minimal admissible set cannot have precisely two
odd generators. -/
theorem odd_card_ne_two {A : Finset ℕ}
    (hA : ParityReduction.SumInjective A) (hlocal : LocallyMinimal A) :
    (A.filter (fun x => x % 2 = 1)).card ≠ 2 := by
  intro hc
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hc
  have haF : a ∈ A.filter (fun x => x % 2 = 1) := by rw [he]; simp
  have hbF : b ∈ A.filter (fun x => x % 2 = 1) := by rw [he]; simp
  have ha := Finset.mem_filter.mp haF
  have hb := Finset.mem_filter.mp hbF
  have hdiv : ∀ x ∈ (A.erase b).erase a, 2 ∣ x := by
    intro x hx
    obtain ⟨hxa, hxb, hxA⟩ := (Finset.mem_erase.mp hx).imp_right Finset.mem_erase.mp
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hxodd : x % 2 ≠ 1 := by
      intro ho
      have hxF : x ∈ A.filter (fun x => x % 2 = 1) := Finset.mem_filter.mpr ⟨hxA, ho⟩
      rw [he] at hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxF
      tauto
    omega
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact no_two_congruent_exceptions (d := 2) hA hlocal ha.1 hb.1 hab
      (by simp only [Nat.dvd_iff_mod_eq_zero, ha.2]; omega)
      (Nat.dvd_iff_mod_eq_zero.mpr (by omega)) hdiv
  · apply no_two_congruent_exceptions (d := 2) hA hlocal hb.1 ha.1 hba
      (by simp only [Nat.dvd_iff_mod_eq_zero, hb.2]; omega)
      (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    intro x hx
    apply hdiv x
    simp only [Finset.mem_erase] at hx ⊢
    tauto

/-- If a locally minimal admissible set has only one odd generator, that
generator must be `1`. -/
theorem unique_odd_eq_one {A : Finset ℕ} {a : ℕ}
    (hlocal : LocallyMinimal A) (ha : a ∈ A) (haodd : a % 2 = 1)
    (hodd : ∀ x ∈ A, x % 2 = 1 → x = a) : a = 1 := by
  by_contra hne
  have ha1 : 1 < a := by omega
  have he : 2 = 1 := common_divisor_erase_eq_one hlocal ha ha1 (by
    intro x hx
    obtain ⟨hxa, hx⟩ := Finset.mem_erase.mp hx
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have ho := hodd x hx
    omega)
  omega

end LocalReduction

/-- This reduction is valid for every admissible set; the uniform bound for
locally minimal sets is still unproved. -/
theorem uniform_bound_locallyMinimal_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → LocalReduction.LocallyMinimal A → 2 ^ A.card ≤ K * N) := by
  rw [uniform_bound_iff]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun N A hA hN _ => hK N A hA hN⟩
  · rintro ⟨K, hK⟩
    refine ⟨K, fun N A hA hN => ?_⟩
    obtain ⟨B, hB, hcard, _, hlocal⟩ := LocalReduction.exists_locallyMinimal hA
    simpa only [hcard] using hK N B hB hN hlocal

/-- Failure of the original conjecture would also give locally minimal
counterexamples for every proposed integer constant. -/
theorem negation_locallyMinimal_iff :
    (¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∀ K : ℕ, ∃ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N ∧
      N ≠ 0 ∧ LocalReduction.LocallyMinimal A ∧ K * N < 2 ^ A.card) := by
  rw [uniform_bound_locallyMinimal_iff]
  push_neg
  rfl


namespace WeakReduction

/-- Subset sums of the same cardinality are different. No assertion is made
about subsets of different cardinalities. -/
def WeaklySumDistinct (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, ∀ T ⊆ A, S.card = T.card → S.sum id = T.sum id → S = T

lemma weak_mono {A B : Finset ℕ} (h : WeaklySumDistinct A) (hB : B ⊆ A) :
    WeaklySumDistinct B := by
  intro S hS T hT hc he
  exact h S (hS.trans hB) T (hT.trans hB) hc he

lemma weak_of_sum_injective {A : Finset ℕ} (h : ParityReduction.SumInjective A) :
    WeaklySumDistinct A := by
  intro S hS T hT _ he
  exact (ParityReduction.sums_eq_iff h hS hT).mp he

/-- The only new equal-cardinality collisions on adjoining `a` are between
subsets whose old cardinalities differ by one. -/
lemma weak_insert_iff {C : Finset ℕ} {a : ℕ} (ha : a ∉ C)
    (hC : WeaklySumDistinct C) :
    WeaklySumDistinct (insert a C) ↔
      ∀ S ⊆ C, ∀ T ⊆ C, S.card + 1 = T.card → a + S.sum id ≠ T.sum id := by
  constructor
  · intro h S hS T hT hc he
    have haS : a ∉ S := fun hm => ha (hS hm)
    have hs : insert a S ⊆ insert a C := Finset.insert_subset_insert a hS
    have ht : T ⊆ insert a C := hT.trans (Finset.subset_insert _ _)
    have heq := h (insert a S) hs T ht
      (by simpa only [Finset.card_insert_of_notMem haS] using hc)
      (by simpa only [Finset.sum_insert haS, id_eq] using he)
    exact ha (hT (heq ▸ Finset.mem_insert_self a S))
  · intro h S hS T hT hc he
    by_cases haS : a ∈ S
    · have hS' : S.erase a ⊆ C := by
        intro x hx
        obtain ⟨hxa, hx⟩ := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (hS hx)).resolve_left hxa
      have hs := Finset.sum_erase_add S id haS
      have hsc := Finset.card_erase_of_mem haS
      have hspos := Finset.card_pos.mpr ⟨a, haS⟩
      by_cases haT : a ∈ T
      · have hT' : T.erase a ⊆ C := by
          intro x hx
          obtain ⟨hxa, hx⟩ := Finset.mem_erase.mp hx
          exact (Finset.mem_insert.mp (hT hx)).resolve_left hxa
        have ht := Finset.sum_erase_add T id haT
        have htc := Finset.card_erase_of_mem haT
        have hEq := hC (S.erase a) hS' (T.erase a) hT' (by omega) (by
          simp only [id_eq] at hs ht he ⊢
          omega)
        simpa only [Finset.insert_erase haS, Finset.insert_erase haT] using
          congrArg (insert a) hEq
      · have hT' : T ⊆ C := (Finset.subset_insert_iff_of_notMem haT).mp hT
        exfalso
        apply h (S.erase a) hS' T hT' (by omega)
        simp only [id_eq] at hs he ⊢
        omega
    · have hS' : S ⊆ C := (Finset.subset_insert_iff_of_notMem haS).mp hS
      by_cases haT : a ∈ T
      · have hT' : T.erase a ⊆ C := by
          intro x hx
          obtain ⟨hxa, hx⟩ := Finset.mem_erase.mp hx
          exact (Finset.mem_insert.mp (hT hx)).resolve_left hxa
        have ht := Finset.sum_erase_add T id haT
        have htc := Finset.card_erase_of_mem haT
        have htpos := Finset.card_pos.mpr ⟨a, haT⟩
        exfalso
        apply h (T.erase a) hT' S hS' (by omega)
        simp only [id_eq] at ht he ⊢
        omega
      · exact hC S hS' T ((Finset.subset_insert_iff_of_notMem haT).mp hT) hc he

/-- An exact missing-sum criterion. The subsets `S` and `U` may overlap;
requiring disjointness here would be incorrect. -/
theorem weak_insert_iff_missing_balanced_sum {C : Finset ℕ} {a : ℕ}
    (ha : a ∉ C) (hC : WeaklySumDistinct C) :
    WeaklySumDistinct (insert a C) ↔
      ∀ S ⊆ C, ∀ U ⊆ C, S.card + U.card + 1 = C.card →
        a + S.sum id + U.sum id ≠ C.sum id := by
  rw [weak_insert_iff ha hC]
  constructor
  · intro h S hS U hU hc he
    have hcu := Finset.card_sdiff_add_card_eq_card hU
    have hsu := Finset.sum_sdiff (f := id) hU
    apply h S hS (C \ U) Finset.sdiff_subset (by omega)
    simp only [id_eq] at hsu he ⊢
    omega
  · intro h S hS T hT hc he
    have hct := Finset.card_sdiff_add_card_eq_card hT
    have hst := Finset.sum_sdiff (f := id) hT
    apply h S hS (C \ T) Finset.sdiff_subset (by omega)
    simp only [id_eq] at hst he ⊢
    omega

/-- Translation by one more than the total sum separates cardinalities. -/
def offsetSet (A : Finset ℕ) : Finset ℕ :=
  A.image (fun a => A.sum id + 1 + a)

lemma offsetSet_card (A : Finset ℕ) : (offsetSet A).card = A.card := by
  exact Finset.card_image_of_injective _ (fun _ _ he => Nat.add_left_cancel he)

lemma offset_sum (A S : Finset ℕ) :
    (S.image (fun a => A.sum id + 1 + a)).sum id =
      S.card * (A.sum id + 1) + S.sum id := by
  rw [Finset.sum_image (fun _ _ _ _ he => Nat.add_left_cancel he)]
  change (∑ x ∈ S, ((A.sum id + 1) + x)) = _
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul, Nat.cast_id, id_eq]

/-- An admissible set of the same cardinality with ambient bound `2 * sum A + 1`. -/
theorem offsetSet_sum_distinct {A : Finset ℕ} (hA : WeaklySumDistinct A) :
    IsSumDistinctSet (offsetSet A) (2 * A.sum id + 1) := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hle : a ≤ A.sum id := by
      simpa using (Finset.single_le_sum (fun x _ => Nat.zero_le (id x)) ha)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro S T he
    obtain ⟨s, hs, hsim⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp S.property)
    obtain ⟨t, ht, htim⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp T.property)
    apply Subtype.ext
    change S.val = T.val
    change S.val.sum id = T.val.sum id at he
    rw [← hsim, ← htim, offset_sum, offset_sum] at he
    have hsle : s.sum id < A.sum id + 1 := by
      exact Nat.lt_succ_of_le (Finset.sum_le_sum_of_subset (f := id) hs)
    have htle : t.sum id < A.sum id + 1 := by
      exact Nat.lt_succ_of_le (Finset.sum_le_sum_of_subset (f := id) ht)
    have hc := congrArg (fun x => x / (A.sum id + 1)) he
    dsimp only at hc
    rw [Nat.mul_comm s.card, Nat.mul_comm t.card,
      Nat.mul_add_div (by omega : 0 < A.sum id + 1),
      Nat.mul_add_div (by omega : 0 < A.sum id + 1),
      Nat.div_eq_of_lt hsle, Nat.div_eq_of_lt htle] at hc
    simp only [add_zero] at hc
    have hst : s = t := hA s hs t ht hc (by
      rw [hc] at he
      exact Nat.add_left_cancel he)
    rw [← hsim, ← htim, hst]

/-- A sufficient criterion for disproof. The hypothesis requires an unbounded
improvement in total sum; no family satisfying it has been constructed. -/
theorem negation_of_weak_examples
    (h : ∀ K : ℕ, ∃ A : Finset ℕ,
      WeaklySumDistinct A ∧ K * (A.sum id + 1) < 2 ^ A.card) :
    ¬ ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N := by
  rw [negation_iff]
  intro K
  obtain ⟨A, hA, hbad⟩ := h (2 * K)
  refine ⟨2 * A.sum id + 1, offsetSet A, offsetSet_sum_distinct hA, by omega, ?_⟩
  rw [offsetSet_card]
  nlinarith

end WeakReduction

namespace WeakReduction

/-- If two generators have representations of the same size, the representation
of the larger generator must contain the smaller one. -/
lemma smaller_mem_representation {A S T : Finset ℕ} {a b : ℕ}
    (hA : WeaklySumDistinct A) (ha : a ∈ A) (hb : b ∈ A) (hab : a < b)
    (hS : S ⊆ A.erase a) (hT : T ⊆ A.erase b)
    (hc : S.card = T.card) (hs : S.sum id = a) (ht : T.sum id = b) : a ∈ T := by
  have hbS : b ∉ S := by
    intro hm
    have hle : b ≤ S.sum id := by
      simpa using (Finset.single_le_sum (fun x _ => Nat.zero_le (id x)) hm)
    omega
  have hbT : b ∉ T := fun hm => Finset.notMem_erase b A (hT hm)
  by_contra haT
  have hEq := hA (insert b S)
    (Finset.insert_subset hb (hS.trans (Finset.erase_subset _ _)))
    (insert a T) (Finset.insert_subset ha (hT.trans (Finset.erase_subset _ _)))
    (by simpa only [Finset.card_insert_of_notMem hbS,
      Finset.card_insert_of_notMem haT] using congrArg (· + 1) hc)
    (by simp only [Finset.sum_insert hbS, Finset.sum_insert haT, id_eq] at hs ht ⊢
        omega)
  have hbm : b ∈ insert a T := hEq ▸ Finset.mem_insert_self b S
  rcases Finset.mem_insert.mp hbm with he | hm
  · omega
  · exact hbT hm

/-- There are at most `r+1` generators that can each be written as a sum of
exactly `r` other generators. -/
theorem card_generators_with_r_term_representation_le {A B : Finset ℕ} {r : ℕ}
    (hA : WeaklySumDistinct A) (hB : B ⊆ A)
    (hrep : ∀ b ∈ B, ∃ T ⊆ A.erase b, T.card = r ∧ T.sum id = b) :
    B.card ≤ r + 1 := by
  by_cases hne : B.Nonempty
  · let b := B.max' hne
    have hb : b ∈ B := B.max'_mem hne
    obtain ⟨T, hT, hTc, hTs⟩ := hrep b hb
    have hsub : B.erase b ⊆ T := by
      intro a ha
      obtain ⟨hab, ha⟩ := Finset.mem_erase.mp ha
      obtain ⟨S, hS, hSc, hSs⟩ := hrep a ha
      have hle : a ≤ b := B.le_max' a ha
      exact smaller_mem_representation hA (hB ha) (hB hb) (by omega)
        hS hT (hSc.trans hTc.symm) hSs hTs
    have hcard := Finset.card_le_card hsub
    have he := Finset.card_erase_add_one hb
    omega
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.card_empty]
    omega

/-- Summing over possible arities gives a quadratic bound. No disjointness
between representations of different arities is assumed. -/
theorem card_generators_with_short_representation_le {A B : Finset ℕ} {r : ℕ}
    (hA : WeaklySumDistinct A) (hB : B ⊆ A)
    (hrep : ∀ b ∈ B, ∃ T ⊆ A.erase b, T.card ≤ r ∧ T.sum id = b) :
    2 * B.card ≤ (r + 1) * (r + 2) := by
  classical
  let F : ℕ → Finset ℕ := fun j => B.filter
    (fun b => ∃ T ⊆ A.erase b, T.card = j ∧ T.sum id = b)
  have hF (j : ℕ) : (F j).card ≤ j + 1 := by
    apply card_generators_with_r_term_representation_le hA
      ((Finset.filter_subset _ _).trans hB)
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  have hcover : B ⊆ (Finset.range (r + 1)).biUnion F := by
    intro b hb
    obtain ⟨T, hT, hTc, hTs⟩ := hrep b hb
    exact Finset.mem_biUnion.mpr ⟨T.card, Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨hb, T, hT, rfl, hTs⟩⟩
  have hc : B.card ≤ ∑ j ∈ Finset.range (r + 1), (j + 1) := by
    exact (Finset.card_le_card hcover).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun j _ => hF j)))
  have ht := Finset.sum_range_id_mul_two (r + 1)
  simp only [Nat.add_sub_cancel] at ht
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_id, mul_one] at hc
  nlinarith

end WeakReduction


/- Spectral bounds for families avoiding antipodal and near-antipodal pairs.
This development targets a dimension-dependent bound, not the uniform
Erdős distinct-subset-sums conjecture. -/
namespace CubeInertia
open Finset Matrix
set_option maxHeartbeats 1000000

/-- Restricting an isotropic subspace to the nonpositive coordinates is injective. -/
theorem isotropic_dimension_bound {α β : Type*} [Fintype α] [Fintype β]
    (U : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (hU : Function.Injective U) (w : β → ℝ)
    (hw : ∀ x, ∑ i, w i * (U x i) ^ 2 = 0) :
    Fintype.card α ≤ Fintype.card {i // w i ≤ 0} := by
  classical
  let L : (α → ℝ) →ₗ[ℝ] ({i // w i ≤ 0} → ℝ) :=
    { toFun := fun x i => U x i
      map_add' := by intros; ext i; simp
      map_smul' := by intros; ext i; simp }
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hzero (i : β) (hi : w i ≤ 0) : U x i = 0 := congrFun hx ⟨i, hi⟩
    have hnonneg (i : β) : 0 ≤ w i * (U x i) ^ 2 := by
      by_cases hi : w i ≤ 0
      · rw [hzero i hi]; simp
      · exact mul_nonneg (le_of_lt (lt_of_not_ge hi)) (sq_nonneg _)
    have hu : U x = 0 := by
      funext i
      by_cases hi : w i ≤ 0
      · exact hzero i hi
      · have he : w i * (U x i) ^ 2 = 0 := by
          have hle := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
          rw [hw] at hle
          exact le_antisymm hle (hnonneg i)
        have hsq := (mul_eq_zero.mp he).resolve_left (ne_of_gt (lt_of_not_ge hi))
        exact eq_zero_of_pow_eq_zero hsq
    exact hU (by simpa using hu)
  simpa using L.finrank_le_finrank_of_injective hL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signAt (s : Finset ι) (i : ι) : ℝ := if i ∈ s then -1 else 1

def character (s x : Finset ι) : ℝ := ∏ i ∈ x, signAt s i

omit [Fintype ι] in
lemma signAt_sq (s : Finset ι) (i : ι) : signAt s i * signAt s i = 1 := by
  by_cases hi : i ∈ s <;> simp [signAt, hi]

omit [Fintype ι] in
lemma character_sq (s x : Finset ι) : character s x * character s x = 1 := by
  rw [character, ← Finset.prod_mul_distrib]
  simp only [signAt_sq, Finset.prod_const_one]

omit [Fintype ι] in
lemma character_eq_pow (s x : Finset ι) : character s x = (-1 : ℝ) ^ (x ∩ s).card := by
  simp [character, signAt]

omit [Fintype ι] in
lemma character_symm (s x : Finset ι) : character s x = character x s := by
  simp only [character_eq_pow, Finset.inter_comm]

lemma character_univ (s : Finset ι) : character s univ = (-1 : ℝ) ^ s.card := by
  simp [character_eq_pow]

lemma character_compl (s x : Finset ι) :
    character s xᶜ = (-1 : ℝ) ^ s.card * character s x := by
  have he : character s x * character s xᶜ = character s univ := by
    exact Finset.prod_mul_prod_compl x (signAt s)
  rw [character_univ] at he
  have hsq := character_sq s x
  calc
    character s xᶜ = (character s x * character s x) * character s xᶜ := by rw [hsq, one_mul]
    _ = character s x * (character s x * character s xᶜ) := by ring
    _ = character s x * (-1 : ℝ) ^ s.card := by rw [he]
    _ = _ := by ring

lemma character_orthogonal (s t : Finset ι) :
    ∑ x : Finset ι, character s x * character t x =
      if s = t then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext; simp
  simp only [character, ← Finset.prod_mul_distrib]
  rw [hpow, ← Finset.prod_one_add]
  by_cases hst : s = t
  · subst t
    norm_num [signAt_sq]
  · rw [if_neg hst]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ s ↔ i ∈ t) := by
      by_contra h
      push_neg at h
      exact hst (Finset.ext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [signAt]

noncomputable def walsh : Matrix (Finset ι) (Finset ι) ℝ := character

lemma walsh_sq : (walsh (ι := ι)) * walsh = (2 : ℝ) ^ Fintype.card ι • 1 := by
  ext s t
  simp only [Matrix.mul_apply, walsh, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [show ∀ x, character x t = character t x from fun x => character_symm x t]
  rw [character_orthogonal]
  split_ifs <;> simp


def flip (x : Finset ι) (i : ι) : Finset ι :=
  if i ∈ x then x.erase i else insert i x

omit [Fintype ι] in
lemma character_flip (s x : Finset ι) (i : ι) :
    character s (flip x i) = signAt s i * character s x := by
  by_cases hi : i ∈ x
  · have he : signAt s i * character s (x.erase i) = character s x :=
      Finset.mul_prod_erase x (signAt s) hi
    have hsq := signAt_sq s i
    simp only [flip, if_pos hi]
    calc
      character s (x.erase i) = (signAt s i * signAt s i) * character s (x.erase i) := by
        rw [hsq, one_mul]
      _ = signAt s i * (signAt s i * character s (x.erase i)) := by ring
      _ = _ := by rw [he]
  · simp [flip, hi, character, Finset.prod_insert]

lemma signAt_sum (s : Finset ι) :
    (∑ i, signAt s i) = (Fintype.card ι : ℝ) - 2 * s.card := by
  have he (i : ι) : signAt s i = 1 - 2 * (if i ∈ s then (1 : ℝ) else 0) := by
    by_cases hi : i ∈ s <;> norm_num [signAt, hi]
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

noncomputable def eigenvalue (c : ℝ) (s : Finset ι) : ℝ :=
  (-1 : ℝ) ^ s.card * ((Fintype.card ι : ℝ) + c - 2 * s.card)

lemma character_eigenvalue (c : ℝ) (s x : Finset ι) :
    c * character s xᶜ + (∑ i, character s (flip xᶜ i)) =
      eigenvalue c s * character s x := by
  simp_rw [character_flip, character_compl]
  rw [← Finset.sum_mul, signAt_sum]
  dsimp [eigenvalue]
  ring

lemma spectral_kernel_zero (c : ℝ) (x y : Finset ι)
    (hc : c = 0 ∨ x ≠ yᶜ) (hxy : ∀ i, x ≠ flip yᶜ i) :
    (∑ s : Finset ι, eigenvalue c s * character s x * character s y) = 0 := by
  have horth (z : Finset ι) : (∑ s : Finset ι, character s x * character s z) =
      if x = z then (2 : ℝ) ^ Fintype.card ι else 0 := by
    simp_rw [show ∀ s, character s x = character x s from fun s => character_symm s x,
      show ∀ s, character s z = character z s from fun s => character_symm s z]
    exact character_orthogonal x z
  have he : (∑ s : Finset ι, eigenvalue c s * character s x * character s y) =
      c * (∑ s : Finset ι, character s x * character s yᶜ) +
        ∑ i, ∑ s : Finset ι, character s x * character s (flip yᶜ i) := by
    calc
      _ = ∑ s : Finset ι, character s x * (eigenvalue c s * character s y) := by
        apply sum_congr rfl; intro s _; ring
      _ = ∑ s : Finset ι, character s x *
          (c * character s yᶜ + ∑ i, character s (flip yᶜ i)) := by
        simp_rw [character_eigenvalue]
      _ = _ := by
        simp only [mul_add, mul_sum, sum_add_distrib]
        rw [Finset.sum_comm]
        congr 1
        apply sum_congr rfl; intro s _; ring
  rw [he]
  simp only [horth, hxy, if_false, sum_const_zero, add_zero]
  rcases hc with rfl | hc
  · simp
  · simp [hc]

/-- The exact inertia bound for a family with no near-antipodal pairs.
The additional antipodal restriction is unnecessary when c=0. -/
theorem family_inertia_bound_scaled (F : Finset (Finset ι)) (c r : ℝ)
    (hF : ∀ x ∈ F, ∀ y ∈ F, (c = 0 ∨ x ≠ yᶜ) ∧ ∀ i, x ≠ flip yᶜ i) :
    F.card ≤ Fintype.card {s : Finset ι // r * eigenvalue c s ≤ 0} := by
  classical
  let H : Matrix (Finset ι) F ℝ := fun s x => character s x
  let U : (F → ℝ) →ₗ[ℝ] (Finset ι → ℝ) := Matrix.mulVecLin H
  have hH : H.transpose * H = (2 : ℝ) ^ Fintype.card ι • 1 := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.transpose_apply, H, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply]
    simp_rw [show ∀ s, character s x.val = character x.val s from fun s => character_symm s x.val,
      show ∀ s, character s y.val = character y.val s from fun s => character_symm s y.val]
    rw [character_orthogonal]
    by_cases hxy : x = y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      simp [hxy, hv]
  have hU : Function.Injective U := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := congrArg (fun w => H.transpose *ᵥ w) hv
    change H.transpose *ᵥ (H *ᵥ v) = H.transpose *ᵥ 0 at he
    rw [Matrix.mulVec_mulVec, hH, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at he
    funext x
    have hx := congrFun he x
    change (2 : ℝ) ^ Fintype.card ι * v x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left (by positivity)
  have hk (x y : F) : (∑ s : Finset ι, (r * eigenvalue c s) * character s x * character s y) = 0 := by
    obtain ⟨hanti, hnear⟩ := hF x x.property y y.property
    have he := spectral_kernel_zero (ι := ι) c x.val y.val hanti hnear
    calc
      _ = r * (∑ s : Finset ι, eigenvalue c s * character s x * character s y) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl; intro s _; ring
      _ = 0 := by rw [he, mul_zero]
  have hw (v : F → ℝ) : (∑ s : Finset ι, (r * eigenvalue c s) * (U v s) ^ 2) = 0 := by
    calc
      _ = ∑ s : Finset ι, ∑ x : F, ∑ y : F,
          ((r * eigenvalue c s) * character s x * character s y) * (v x * v y) := by
        simp only [U, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, H,
          pow_two, Finset.sum_mul, Finset.mul_sum]
        apply sum_congr rfl; intro s _
        apply sum_congr rfl; intro x _
        apply sum_congr rfl; intro y _
        ring
      _ = ∑ x : F, ∑ y : F, (∑ s : Finset ι,
          (r * eigenvalue c s) * character s x * character s y) * (v x * v y) := by
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro x _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = 0 := by simp only [hk, zero_mul, sum_const_zero]
  simpa only [Fintype.card_coe] using isotropic_dimension_bound U hU (fun s => r * eigenvalue c s) hw



noncomputable def centralParameter : ℝ :=
  (2 * (Fintype.card ι / 2) + 1 : ℕ) - (Fintype.card ι : ℝ)

def signValue (s : Finset ι) : ℤ :=
  if s.card ≤ Fintype.card ι / 2 then (-1) ^ s.card else -(-1) ^ s.card

omit [DecidableEq ι] in
lemma signValue_cases (s : Finset ι) : signValue s = 1 ∨ signValue s = -1 := by
  have hp : (-1 : ℤ) ^ s.card = 1 ∨ (-1 : ℤ) ^ s.card = -1 :=
    neg_one_pow_eq_or ℤ s.card
  dsimp [signValue]
  split_ifs <;> rcases hp with hp | hp <;> simp [hp]

omit [DecidableEq ι] in
lemma central_eigenvalue (s : Finset ι) :
    eigenvalue (centralParameter (ι := ι)) s =
      (-1 : ℝ) ^ s.card * (2 * (Fintype.card ι / 2 : ℕ) + 1 - 2 * (s.card : ℝ)) := by
  simp only [eigenvalue, centralParameter, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  ring

omit [DecidableEq ι] in
lemma eigenvalue_signValue (s : Finset ι) :
    (signValue s : ℝ) * eigenvalue (centralParameter (ι := ι)) s > 0 := by
  rw [central_eigenvalue]
  have hp : (-1 : ℝ) ^ s.card * (-1 : ℝ) ^ s.card = 1 := by
    rw [← mul_pow]; norm_num
  by_cases hs : s.card ≤ Fintype.card ι / 2
  · have hsR : (s.card : ℝ) ≤ ((Fintype.card ι / 2 : ℕ) : ℝ) := by exact_mod_cast hs
    simp only [signValue, if_pos hs, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [← mul_assoc, hp, one_mul]
    linarith
  · have hsR : (Fintype.card ι / 2 : ℕ) < s.card := by omega
    simp only [signValue, if_neg hs, Int.cast_neg, Int.cast_pow, Int.cast_one]
    have he : -((-1 : ℝ) ^ s.card) *
        ((-1 : ℝ) ^ s.card * (2 * (Fintype.card ι / 2 : ℕ) + 1 - 2 * (s.card : ℝ))) =
        2 * (s.card : ℝ) - (2 * (Fintype.card ι / 2 : ℕ) + 1) := by
      nlinarith only [hp]
    rw [he]
    have hh : ((Fintype.card ι / 2 : ℕ) : ℝ) + 1 ≤ s.card := by exact_mod_cast (Nat.add_one_le_iff.mpr hsR)
    linarith

omit [DecidableEq ι] in
lemma central_nonpos_iff (s : Finset ι) :
    eigenvalue (centralParameter (ι := ι)) s ≤ 0 ↔ signValue s = -1 := by
  have hp := eigenvalue_signValue s
  rcases signValue_cases s with h | h <;> rw [h] at hp ⊢ <;> norm_num at hp ⊢ <;> linarith

omit [DecidableEq ι] in
lemma central_nonneg_iff (s : Finset ι) :
    -eigenvalue (centralParameter (ι := ι)) s ≤ 0 ↔ signValue s = 1 := by
  have hp := eigenvalue_signValue s
  rcases signValue_cases s with h | h <;> rw [h] at hp ⊢ <;> norm_num at hp ⊢ <;> linarith



omit [DecidableEq ι] in
lemma partial_alternating_sum (hn : 0 < Fintype.card ι) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (∑ s : Finset ι, if s.card ≤ k then (-1 : ℤ) ^ s.card else 0) =
      (-1 : ℤ) ^ k * (Fintype.card ι - 1).choose k := by
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext; simp
  rw [hpow, Finset.sum_powerset_apply_card (fun j => if j ≤ k then (-1 : ℤ) ^ j else 0)]
  simp only [Finset.card_univ, nsmul_eq_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hf : (range (Fintype.card ι + 1)).filter (fun j => j ≤ k) = range (k + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [hf]
  have he := Int.alternating_sum_range_choose_eq_choose (n := Fintype.card ι - 1) (m := k)
  rw [Nat.sub_add_cancel hn] at he
  convert he using 1
  apply sum_congr rfl; intro j _; ring

omit [DecidableEq ι] in
lemma signValue_sum (hn : 0 < Fintype.card ι) :
    (∑ s : Finset ι, signValue s) =
      2 * (-1 : ℤ) ^ (Fintype.card ι / 2) * (Fintype.card ι - 1).choose (Fintype.card ι / 2) := by
  have hpow : (univ : Finset (Finset ι)) = (univ : Finset ι).powerset := by ext; simp
  have hzero : (∑ s : Finset ι, (-1 : ℤ) ^ s.card) = 0 := by
    rw [hpow]
    apply Finset.sum_powerset_neg_one_pow_card_of_nonempty
    exact Finset.card_pos.mp (by simpa using hn)
  have he (s : Finset ι) : signValue s =
      2 * (if s.card ≤ Fintype.card ι / 2 then (-1 : ℤ) ^ s.card else 0) - (-1) ^ s.card := by
    dsimp [signValue]
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero,
    partial_alternating_sum hn _ (Nat.div_le_self _ _)]
  ring

def positiveCount : ℕ := ((univ : Finset (Finset ι)).filter (fun s => signValue s = 1)).card

def negativeCount : ℕ := ((univ : Finset (Finset ι)).filter (fun s => signValue s = -1)).card

omit [DecidableEq ι] in
lemma sign_counts_total : (positiveCount (ι := ι) : ℤ) + negativeCount (ι := ι) = 2 ^ Fintype.card ι := by
  have he (s : Finset ι) :
      (if signValue s = 1 then (1 : ℤ) else 0) + (if signValue s = -1 then (1 : ℤ) else 0) = 1 := by
    rcases signValue_cases s with h | h <;> simp [h]
  have hsum : (∑ s : Finset ι,
      ((if signValue s = 1 then (1 : ℤ) else 0) + (if signValue s = -1 then (1 : ℤ) else 0))) =
      ∑ _s : Finset ι, (1 : ℤ) := by simp only [he]
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, positiveCount, negativeCount,
    Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat] using hsum

omit [DecidableEq ι] in
lemma sign_counts_difference (hn : 0 < Fintype.card ι) :
    (positiveCount (ι := ι) : ℤ) - negativeCount (ι := ι) =
      2 * (-1 : ℤ) ^ (Fintype.card ι / 2) * (Fintype.card ι - 1).choose (Fintype.card ι / 2) := by
  rw [← signValue_sum hn]
  have he (s : Finset ι) : signValue s =
      (if signValue s = 1 then (1 : ℤ) else 0) - (if signValue s = -1 then (1 : ℤ) else 0) := by
    rcases signValue_cases s with h | h <;> simp [h]
  symm
  calc
    _ = ∑ s : Finset ι, ((if signValue s = 1 then (1 : ℤ) else 0) -
        (if signValue s = -1 then (1 : ℤ) else 0)) := sum_congr rfl (fun s _ => he s)
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_boole, positiveCount, negativeCount]

/-- Sharp special diameter bound obtained directly from cube inertia. -/
theorem family_sharp_bound (hn : 0 < Fintype.card ι) (F : Finset (Finset ι))
    (hF : ∀ x ∈ F, ∀ y ∈ F, x ≠ yᶜ ∧ ∀ i, x ≠ flip yᶜ i) :
    2 * F.card + 2 * (Fintype.card ι - 1).choose (Fintype.card ι / 2) ≤ 2 ^ Fintype.card ι := by
  have hnF : F.card ≤ negativeCount (ι := ι) := by
    have hh := family_inertia_bound_scaled F (centralParameter (ι := ι)) 1
      (fun x hx y hy => ⟨Or.inr (hF x hx y hy).1, (hF x hx y hy).2⟩)
    simpa only [one_mul, Fintype.card_subtype, central_nonpos_iff, negativeCount] using hh
  have hpF : F.card ≤ positiveCount (ι := ι) := by
    have hh := family_inertia_bound_scaled F (centralParameter (ι := ι)) (-1)
      (fun x hx y hy => ⟨Or.inr (hF x hx y hy).1, (hF x hx y hy).2⟩)
    simpa only [neg_one_mul, Fintype.card_subtype, central_nonneg_iff, positiveCount] using hh
  have ht := sign_counts_total (ι := ι)
  have hd := sign_counts_difference (ι := ι) hn
  have hnZ : (F.card : ℤ) ≤ negativeCount (ι := ι) := by exact_mod_cast hnF
  have hpZ : (F.card : ℤ) ≤ positiveCount (ι := ι) := by exact_mod_cast hpF
  have hout : 2 * (F.card : ℤ) + 2 * (Fintype.card ι - 1).choose (Fintype.card ι / 2) ≤
      (2 : ℤ) ^ Fintype.card ι := by
    rcases neg_one_pow_eq_or ℤ (Fintype.card ι / 2) with h | h <;> rw [h] at hd <;> nlinarith
  exact_mod_cast hout



omit [Fintype ι] in
lemma mem_flip_of_ne (x : Finset ι) {i j : ι} (h : j ≠ i) :
    j ∈ flip x i ↔ j ∈ x := by
  by_cases hi : i ∈ x <;> simp [flip, hi, h]

lemma ne_flip_compl (hn : 2 ≤ Fintype.card ι) (x : Finset ι) (i : ι) :
    x ≠ flip xᶜ i := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  intro he
  have hm : j ∈ x ↔ j ∉ x := by
    calc
      j ∈ x ↔ j ∈ flip xᶜ i := by rw [← he]
      _ ↔ j ∈ xᶜ := mem_flip_of_ne _ hj
      _ ↔ j ∉ x := mem_compl
  tauto

/-- Closed low tail; endpoints are included deliberately. -/
def lowTail (a : ι → ℤ) (N : ℕ) : Finset (Finset ι) :=
  univ.filter (fun S => 2 * ∑ i ∈ S, a i ≤ (∑ i, a i) - N)

def highTail (a : ι → ℤ) (N : ℕ) : Finset (Finset ι) :=
  univ.filter (fun S => (∑ i, a i) + N ≤ 2 * ∑ i ∈ S, a i)

def middleBand (a : ι → ℤ) (N : ℕ) : Finset (Finset ι) :=
  univ.filter (fun S => (∑ i, a i) - N < 2 * ∑ i ∈ S, a i ∧
    2 * ∑ i ∈ S, a i < (∑ i, a i) + N)

lemma sum_flip_compl_lower (a : ι → ℤ) (N : ℕ)
    (ha : ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N) (y : Finset ι) (i : ι) :
    (∑ j, a j) - N ≤ (∑ j ∈ flip yᶜ i, a j) + ∑ j ∈ y, a j := by
  have hc := Finset.sum_add_sum_compl y a
  have hai := ha i
  by_cases hi : i ∈ yᶜ
  · have he := Finset.sum_erase_add yᶜ a hi
    simp only [flip, if_pos hi]
    omega
  · simp only [flip, if_neg hi, Finset.sum_insert hi]
    omega

lemma lowTail_avoids (hn : 2 ≤ Fintype.card ι) (a : ι → ℤ) (N : ℕ)
    (hN : 0 < N) (ha : ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N)
    (hinj : Function.Injective (fun S : Finset ι => ∑ i ∈ S, a i)) :
    ∀ x ∈ lowTail a N, ∀ y ∈ lowTail a N,
      x ≠ yᶜ ∧ ∀ i, x ≠ flip yᶜ i := by
  intro x hx y hy
  have hx' : 2 * ∑ i ∈ x, a i ≤ (∑ i, a i) - N := (mem_filter.mp hx).2
  have hy' : 2 * ∑ i ∈ y, a i ≤ (∑ i, a i) - N := (mem_filter.mp hy).2
  constructor
  · intro he
    have hc := Finset.sum_add_sum_compl y a
    rw [he] at hx'
    omega
  · intro i he
    have hl := sum_flip_compl_lower a N ha y i
    rw [← he] at hl
    have heq : (∑ i ∈ x, a i) = ∑ i ∈ y, a i := by omega
    have hxy := hinj heq
    exact ne_flip_compl hn y i (hxy.symm.trans he)

lemma tails_card_eq (a : ι → ℤ) (N : ℕ) :
    (lowTail a N).card = (highTail a N).card := by
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS
    have hlow := (mem_filter.mp hS).2
    have hc := Finset.sum_add_sum_compl S a
    apply mem_filter.mpr
    exact ⟨mem_univ _, by omega⟩
  · intro S _ T _ he
    exact compl_injective he
  · intro S hS
    have hhigh := (mem_filter.mp hS).2
    have hc := Finset.sum_add_sum_compl S a
    refine ⟨Sᶜ, mem_filter.mpr ⟨mem_univ _, ?_⟩, compl_compl _⟩
    dsimp only at hhigh ⊢
    omega

lemma tails_partition (a : ι → ℤ) (N : ℕ) (hN : 0 < N) :
    2 * (lowTail a N).card + (middleBand a N).card = 2 ^ Fintype.card ι := by
  have pointwise (S : Finset ι) :
      (if S ∈ lowTail a N then (1 : ℕ) else 0) +
      (if S ∈ highTail a N then 1 else 0) +
      (if S ∈ middleBand a N then 1 else 0) = 1 := by
    simp only [lowTail, highTail, middleBand, mem_filter, mem_univ, true_and]
    split_ifs <;> omega
  have hh := congrArg (fun f : Finset ι → ℕ => ∑ S, f S) (funext pointwise)
  simp only [Finset.sum_add_distrib, Finset.sum_boole, filter_mem_eq_inter,
    univ_inter, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    smul_eq_mul, mul_one] at hh
  rw [← tails_card_eq] at hh
  simp only [Nat.cast_id] at hh
  omega

omit [DecidableEq ι] in
lemma middleBand_card_le (a : ι → ℤ) (N : ℕ)
    (hinj : Function.Injective (fun S : Finset ι => ∑ i ∈ S, a i)) :
    (middleBand a N).card ≤ N := by
  have hc : (middleBand a N).card ≤ (Icc (1 : ℤ) (N : ℤ)).card := by
    apply Finset.card_le_card_of_injOn
      (fun S => (∑ i ∈ S, a i) - ((∑ i, a i) - N) / 2)
    · intro S hS
      have hmiddle := (mem_filter.mp hS).2
      change (∑ i ∈ S, a i) - ((∑ i, a i) - N) / 2 ∈ Icc (1 : ℤ) (N : ℤ)
      apply mem_Icc.mpr
      dsimp only at hmiddle ⊢
      omega
    · intro S _ T _ he
      apply hinj
      dsimp only at he ⊢
      omega
  simpa only [Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast] using hc

/-- A sharp central-binomial lower bound for bounded integer weights.
This is dimension-dependent, and is not the uniform Erdős conjecture. -/
theorem indexed_central_binomial_bound (hn : 2 ≤ Fintype.card ι)
    (a : ι → ℤ) (N : ℕ) (hN : 0 < N)
    (ha : ∀ i, -(N : ℤ) ≤ a i ∧ a i ≤ N)
    (hinj : Function.Injective (fun S : Finset ι => ∑ i ∈ S, a i)) :
    2 * (Fintype.card ι - 1).choose (Fintype.card ι / 2) ≤ N := by
  have hl := family_sharp_bound (by omega : 0 < Fintype.card ι) (lowTail a N)
    (lowTail_avoids hn a N hN ha hinj)
  have hp := tails_partition a N hN
  have hm := middleBand_card_le a N hinj
  omega


/-- Finite-set specialization, with the same hypotheses as the conjecture. -/
theorem finset_central_binomial_bound {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N ∧
      (fun (S : A.powerset) => S.val.sum id).Injective)
    (hn : 2 ≤ A.card) (hN : N ≠ 0) :
    2 * (A.card - 1).choose (A.card / 2) ≤ N := by
  let a : A → ℤ := fun i => (i.val : ℤ)
  have hsub (S : Finset A) : S.image Subtype.val ⊆ A := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  have hinj : Function.Injective (fun S : Finset A => ∑ i ∈ S, a i) := by
    intro S T he
    have hsum : (S.image Subtype.val).sum id = (T.image Subtype.val).sum id := by
      rw [Finset.sum_image Subtype.val_injective.injOn,
        Finset.sum_image Subtype.val_injective.injOn]
      dsimp only [a, id_eq] at he ⊢
      exact_mod_cast he
    have hST := congrArg Subtype.val
      (@hA.2 ⟨S.image Subtype.val, Finset.mem_powerset.mpr (hsub S)⟩
        ⟨T.image Subtype.val, Finset.mem_powerset.mpr (hsub T)⟩ hsum)
    exact Finset.image_injective Subtype.val_injective hST
  have hb : ∀ i : A, -(N : ℤ) ≤ a i ∧ a i ≤ N := by
    intro i
    have hi := Finset.mem_Icc.mp (hA.1 i.property)
    dsimp [a]
    constructor
    · omega
    · exact_mod_cast hi.2
  simpa only [Fintype.card_coe] using indexed_central_binomial_bound
    (by simpa only [Fintype.card_coe] using hn) a N (by omega) hb hinj

end CubeInertia

/-- Central-binomial lower bound obtained from Boolean-cube inertia.
This does not provide a dimension-independent constant. -/
theorem central_binomial_bound {A : Finset ℕ} {N : ℕ}
    (hA : IsSumDistinctSet A N) (hn : 2 ≤ A.card) (hN : N ≠ 0) :
    2 * (A.card - 1).choose (A.card / 2) ≤ N :=
  CubeInertia.finset_central_binomial_bound hA hn hN

/--
If $A\subseteq\{1, ..., N\}$ with $|A| = n$ is such that the subset sums $\sum_{a\in S}a$ are
distinct for all $S\subseteq A$ then
$$
  N \gg 2 ^ n.
$$
-/
theorem erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  ↑A ⊆ Set.Ioc (0 : ℝ) N ∧ (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
    1 ≤ dist (S₁.sum id) (S₂.sum id)


/- A proved equivalence with the real minimum-gap formulation.
Neither side of the equivalence is established by these auxiliary results. -/
namespace RealGapReduction
open Finset
set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Separated (a : ι → ℝ) : Prop :=
  ∀ S T : Finset ι, S ≠ T → 1 ≤ |(∑ i ∈ S, a i) - ∑ i ∈ T, a i|

def scale (m : ℕ) : ℕ := 2 ^ m + Fintype.card ι

noncomputable def rounded (a : ι → ℝ) (m : ℕ) (i : ι) : ℕ :=
  ⌊(scale (ι := ι) m : ℝ) * a i⌋₊

omit [DecidableEq ι] in
lemma rounding_bounds (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℕ) (S : Finset ι) :
    ((∑ i ∈ S, rounded a m i : ℕ) : ℝ) ≤ scale (ι := ι) m * ∑ i ∈ S, a i ∧
    scale (ι := ι) m * (∑ i ∈ S, a i) ≤
      ((∑ i ∈ S, rounded a m i : ℕ) : ℝ) + Fintype.card ι := by
  have hnonneg (i : ι) : 0 ≤ (scale (ι := ι) m : ℝ) * a i :=
    mul_nonneg (Nat.cast_nonneg _) (ha i)
  constructor
  · push_cast
    rw [Finset.mul_sum]
    exact sum_le_sum (fun i _ => Nat.floor_le (hnonneg i))
  · have h := sum_le_sum (s := S) (fun i _ => (Nat.lt_floor_add_one
      ((scale (ι := ι) m : ℝ) * a i)).le)
    have hc : (S.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast S.card_le_univ
    simp only [← Finset.mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul,
      mul_one] at h
    push_cast
    change (scale (ι := ι) m : ℝ) * (∑ i ∈ S, a i) ≤
      (∑ i ∈ S, (rounded a m i : ℝ)) + Fintype.card ι
    dsimp [rounded]
    linarith

omit [DecidableEq ι] in
lemma rounded_gap (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a)
    (m : ℕ) (S T : Finset ι) (hST : S ≠ T) :
    (2 : ℝ) ^ m ≤
      |((∑ i ∈ S, rounded a m i : ℕ) : ℝ) - ((∑ i ∈ T, rounded a m i : ℕ) : ℝ)| := by
  obtain ⟨hS₁, hS₂⟩ := rounding_bounds a ha m S
  obtain ⟨hT₁, hT₂⟩ := rounding_bounds a ha m T
  have hq : (0 : ℝ) ≤ scale (ι := ι) m := Nat.cast_nonneg _
  have hscale : (scale (ι := ι) m : ℝ) = (2 : ℝ) ^ m + Fintype.card ι := by
    simp [scale]
  rcases le_abs.mp (hsep S T hST) with h | h
  · have hh := mul_le_mul_of_nonneg_left h hq
    apply le_abs.mpr
    left
    nlinarith only [hh, hS₂, hT₁, hscale]
  · have hh := mul_le_mul_of_nonneg_left h hq
    apply le_abs.mpr
    right
    nlinarith only [hh, hT₂, hS₁, hscale]

private lemma binary_sum_lt {m : ℕ} (S : Finset (Fin m)) :
    ∑ j ∈ S, 2 ^ j.val < 2 ^ m := by
  have hle : ∑ j ∈ S, 2 ^ j.val ≤ ∑ j : Fin m, 2 ^ j.val :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  rw [Fin.sum_univ_eq_sum_range] at hle
  have hgeom := geom_sum_mul_add (R := ℕ) 1 m
  simp only [Nat.reduceAdd, mul_one] at hgeom
  omega

private lemma binary_sum_injective {m : ℕ} :
    Function.Injective (fun S : Finset (Fin m) => ∑ j ∈ S, 2 ^ j.val) := by
  intro S T h
  have he : S.image Fin.val = T.image Fin.val := by
    apply Finset.geomSum_injective (by omega : 2 ≤ (2 : ℕ))
    simpa only [Finset.sum_image Fin.val_injective.injOn] using h
  exact Finset.image_injective Fin.val_injective he

noncomputable def weight (a : ι → ℝ) (m : ℕ) : ι ⊕ Fin m → ℕ :=
  Sum.elim (rounded a m) (fun j => 2 ^ j.val)

lemma indexed_sum_injective (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a)
    (m : ℕ) : Function.Injective (fun S : Finset (ι ⊕ Fin m) => ∑ i ∈ S, weight a m i) := by
  intro S T h
  change (∑ i ∈ S, weight a m i) = ∑ i ∈ T, weight a m i at h
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight,
    Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at h
  change (∑ i ∈ S.toLeft, rounded a m i) + (∑ j ∈ S.toRight, 2 ^ j.val) =
    (∑ i ∈ T.toLeft, rounded a m i) + (∑ j ∈ T.toRight, 2 ^ j.val) at h
  have hleft : S.toLeft = T.toLeft := by
    by_contra hne
    have hgap := rounded_gap a ha hsep m S.toLeft T.toLeft hne
    have hloS : (0 : ℝ) ≤ (∑ j ∈ S.toRight, 2 ^ j.val : ℕ) := Nat.cast_nonneg _
    have hloT : (0 : ℝ) ≤ (∑ j ∈ T.toRight, 2 ^ j.val : ℕ) := Nat.cast_nonneg _
    have hhiS : ((∑ j ∈ S.toRight, 2 ^ j.val : ℕ) : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast binary_sum_lt S.toRight
    have hhiT : ((∑ j ∈ T.toRight, 2 ^ j.val : ℕ) : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast binary_sum_lt T.toRight
    have he : ((∑ i ∈ S.toLeft, rounded a m i : ℕ) : ℝ) +
        (∑ j ∈ S.toRight, 2 ^ j.val : ℕ) =
        ((∑ i ∈ T.toLeft, rounded a m i : ℕ) : ℝ) + (∑ j ∈ T.toRight, 2 ^ j.val : ℕ) := by
      exact_mod_cast h
    have hlt : |((∑ i ∈ S.toLeft, rounded a m i : ℕ) : ℝ) -
        ((∑ i ∈ T.toLeft, rounded a m i : ℕ) : ℝ)| < (2 : ℝ) ^ m := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge hgap) hlt
  have hright : S.toRight = T.toRight := by
    apply binary_sum_injective
    rw [hleft] at h
    exact Nat.add_left_cancel h
  rw [← S.toLeft_disjSum_toRight, ← T.toLeft_disjSum_toRight, hleft, hright]

noncomputable def integerSet (a : ι → ℝ) (m : ℕ) : Finset ℕ :=
  Finset.univ.image (weight a m)

lemma weight_injective (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a) (m : ℕ) :
    Function.Injective (weight a m) := by
  intro i j h
  apply Finset.singleton_injective
  apply indexed_sum_injective a ha hsep m
  simpa only [Finset.sum_singleton] using h

lemma weight_pos (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a)
    (m : ℕ) (i : ι ⊕ Fin m) : 0 < weight a m i := by
  by_contra h
  have hz : weight a m i = 0 := by omega
  have he : ({i} : Finset (ι ⊕ Fin m)) = ∅ :=
    indexed_sum_injective a ha hsep m (by simpa using hz)
  exact Finset.singleton_ne_empty i he

lemma integerSet_card (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a) (m : ℕ) :
    (integerSet a m).card = Fintype.card ι + m := by
  rw [integerSet, Finset.card_image_of_injective _ (weight_injective a ha hsep m)]
  simp

lemma integerSet_sum_injective (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsep : Separated a) (m : ℕ) :
    (fun S : (integerSet a m).powerset => S.val.sum id).Injective := by
  intro S T hST
  obtain ⟨s, _, hs⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp S.property)
  obtain ⟨t, _, ht⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp T.property)
  apply Subtype.ext
  change S.val.sum id = T.val.sum id at hST
  rw [← hs, ← ht, Finset.sum_image (weight_injective a ha hsep m).injOn,
    Finset.sum_image (weight_injective a ha hsep m).injOn] at hST
  have heq := indexed_sum_injective a ha hsep m hST
  rw [← hs, ← ht, heq]

lemma integerSet_bound (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a)
    (m : ℕ) {R : ℝ} (hR : 1 ≤ R) (haR : ∀ i, a i ≤ R) :
    integerSet a m ⊆ Finset.Icc 1 ⌈(scale (ι := ι) m : ℝ) * R⌉₊ := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_Icc.mpr ⟨weight_pos a ha hsep m i, ?_⟩
  rcases i with i | j
  · change ⌊(scale (ι := ι) m : ℝ) * a i⌋₊ ≤ _
    exact (Nat.floor_mono (mul_le_mul_of_nonneg_left (haR i) (Nat.cast_nonneg _))).trans
      (Nat.floor_le_ceil _)
  · change 2 ^ j.val ≤ _
    have hle : (2 ^ j.val : ℕ) ≤ scale (ι := ι) m :=
      (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ m)).trans (Nat.le_add_right _ _)
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      ((2 ^ j.val : ℕ) : ℝ) ≤ scale (ι := ι) m := by exact_mod_cast hle
      _ ≤ (scale (ι := ι) m : ℝ) * R := by nlinarith [Nat.cast_nonneg (α := ℝ) (scale (ι := ι) m)]
      _ ≤ _ := Nat.le_ceil _


/-- A uniform integer constant also bounds every separated indexed real system.
The cardinality is allowed to grow while the rounding error becomes negligible. -/
theorem indexed_real_bound_of_integer_bound (C : ℝ)
    (hC : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → N ≠ 0 →
      C * 2 ^ A.card ≤ N)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsep : Separated a)
    {R : ℝ} (hR : 1 ≤ R) (haR : ∀ i, a i ≤ R) :
    C * 2 ^ Fintype.card ι ≤ R := by
  have hm (m : ℕ) :
      C * 2 ^ (Fintype.card ι + m) ≤ ((2 : ℝ) ^ m + Fintype.card ι) * R + 1 := by
    have hq : (1 : ℝ) ≤ scale (ι := ι) m := by
      have hpow : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      exact_mod_cast (hpow.trans (Nat.le_add_right _ _))
    have hpos : 0 < (scale (ι := ι) m : ℝ) * R := by positivity
    have hN : ⌈(scale (ι := ι) m : ℝ) * R⌉₊ ≠ 0 := by
      exact Nat.ne_of_gt (Nat.ceil_pos.mpr hpos)
    have h := hC _ _ ⟨integerSet_bound a ha hsep m hR haR,
      integerSet_sum_injective a ha hsep m⟩ hN
    rw [integerSet_card a ha hsep m] at h
    have hceil := (Nat.ceil_lt_add_one hpos.le).le
    calc
      C * 2 ^ (Fintype.card ι + m) ≤ (⌈(scale (ι := ι) m : ℝ) * R⌉₊ : ℝ) := h
      _ ≤ (scale (ι := ι) m : ℝ) * R + 1 := hceil
      _ = _ := by simp [scale]
  by_contra hbad
  have hδ : 0 < C * 2 ^ Fintype.card ι - R := sub_pos.mpr (lt_of_not_ge hbad)
  obtain ⟨m, hm'⟩ := pow_unbounded_of_one_lt
    (((Fintype.card ι : ℝ) * R + 1) / (C * 2 ^ Fintype.card ι - R)) (by norm_num : (1 : ℝ) < 2)
  have hmul := (div_lt_iff₀ hδ).mp hm'
  have h := hm m
  rw [pow_add] at h
  nlinarith only [h, hmul]



lemma separated_subtype {A : Finset ℝ} {N : ℕ} (hA : IsSumDistinctRealSet A N) :
    Separated (fun i : A => (i : ℝ)) := by
  classical
  intro S T hST
  have hsub (s : Finset A) : s.image Subtype.val ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact i.property
  have hne : S.image Subtype.val ≠ T.image Subtype.val :=
    fun he => hST (Finset.image_injective Subtype.val_injective he)
  have h := hA.2 (Finset.mem_powerset.mpr (hsub S)) (Finset.mem_powerset.mpr (hsub T)) hne
  simpa only [Real.dist_eq, Finset.sum_image Subtype.val_injective.injOn, id_eq] using h

/-- The same weak constant transfers from integer sets to the real minimum-gap version. -/
theorem real_bound_of_integer_bound (C : ℝ)
    (hC : ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N → N ≠ 0 →
      C * 2 ^ A.card ≤ N)
    (N : ℕ) (A : Finset ℝ) (hA : IsSumDistinctRealSet A N) (hN : N ≠ 0) :
    C * 2 ^ A.card ≤ N := by
  classical
  have hnonneg (i : A) : 0 ≤ (i : ℝ) := (hA.1 i.property).1.le
  have hbound (i : A) : (i : ℝ) ≤ N := (hA.1 i.property).2
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  simpa using indexed_real_bound_of_integer_bound C hC (fun i : A => (i : ℝ))
    hnonneg (separated_subtype hA) hNR hbound

lemma natural_cast_sum_distinct {A : Finset ℕ} {N : ℕ} (hA : IsSumDistinctSet A N) :
    IsSumDistinctRealSet (A.image (fun n : ℕ => (n : ℝ))) N := by
  classical
  have hcast : Function.Injective (fun n : ℕ => (n : ℝ)) := Nat.cast_injective
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hA.1 ha)
    constructor
    · exact_mod_cast (by omega : 0 < a)
    · exact_mod_cast haN
  · intro S hS T hT hST
    obtain ⟨s, hs, hsi⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp hS)
    obtain ⟨t, ht, hti⟩ := Finset.subset_image_iff.mp (Finset.mem_powerset.mp hT)
    have hne : s.sum id ≠ t.sum id := by
      intro he
      have heq : s = t := congrArg Subtype.val
        (@hA.2 ⟨s, Finset.mem_powerset.mpr hs⟩ ⟨t, Finset.mem_powerset.mpr ht⟩ he)
      exact hST (by rw [← hsi, ← hti, heq])
    rw [← hsi, ← hti, Real.dist_eq, Finset.sum_image hcast.injOn,
      Finset.sum_image hcast.injOn]
    change 1 ≤ |(∑ i ∈ s, (i : ℝ)) - ∑ i ∈ t, (i : ℝ)|
    have hsCast : (∑ i ∈ s, (i : ℝ)) = ((s.sum id : ℕ) : ℝ) := by simp
    have htCast : (∑ i ∈ t, (i : ℝ)) = ((t.sum id : ℕ) : ℝ) := by simp
    rw [hsCast, htCast]
    apply le_abs.mpr
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · right
      have hh : ((s.sum id : ℕ) : ℝ) + 1 ≤ ((t.sum id : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_one_le_iff.mpr hlt)
      linarith
    · left
      have hh : ((t.sum id : ℕ) : ℝ) + 1 ≤ ((s.sum id : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_one_le_iff.mpr hgt)
      linarith

/-- At the level of uniform constants, the integer conjecture and its real
minimum-gap version are equivalent. This does not assert either side. -/
theorem uniform_integer_real_iff :
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) ↔
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℝ), IsSumDistinctRealSet A N →
      N ≠ 0 → C * 2 ^ A.card < N) := by
  classical
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C / 2, by positivity, fun N A hA hN => ?_⟩
    have hb := real_bound_of_integer_bound C (fun N A hA hN => (h N A hA hN).le) N A hA hN
    have hp : 0 < (2 : ℝ) ^ A.card := by positivity
    nlinarith only [hb, mul_pos hC hp]
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun N A hA hN => ?_⟩
    have hb := h N (A.image (fun n : ℕ => (n : ℝ))) (natural_cast_sum_distinct hA) hN
    rwa [Finset.card_image_of_injective _ (Nat.cast_injective (R := ℝ))] at hb


end RealGapReduction

end Erdos1
