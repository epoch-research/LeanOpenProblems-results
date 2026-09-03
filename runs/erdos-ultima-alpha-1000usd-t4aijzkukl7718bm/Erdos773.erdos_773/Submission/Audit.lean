import FormalConjecturesUtil

/-!
# Erdős Problem 773

*Reference:* [erdosproblems.com/773](https://www.erdosproblems.com/773)
-/

namespace Erdos773

set_option maxHeartbeats 1000000

lemma delete_forbidden_edges {α : Type*} [DecidableEq α]
    (A : Finset α) (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty) :
    ∃ B ⊆ A, A.card ≤ B.card + H.card ∧ ∀ e ∈ H, ¬e ⊆ B := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨A, Finset.Subset.refl A, by simp, by simp⟩
  | @insert e H he ih =>
    obtain ⟨B, hBA, hcard, havoid⟩ := ih (fun f hf => hH f (Finset.mem_insert_of_mem hf))
    obtain ⟨a, ha⟩ := hH e (Finset.mem_insert_self e H)
    refine ⟨B.erase a, (Finset.erase_subset a B).trans hBA, ?_, ?_⟩
    · have hc : B.card ≤ (B.erase a).card + 1 := by
        by_cases hab : a ∈ B
        · rw [Finset.card_erase_of_mem hab]
          have : 0 < B.card := Finset.card_pos.mpr ⟨a, hab⟩
          omega
        · simp [Finset.erase_eq_of_notMem hab]
      rw [Finset.card_insert_of_notMem he]
      omega
    · intro f hf hfB
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Finset.notMem_erase a B (hfB ha)
      · exact havoid f hf (hfB.trans (Finset.erase_subset a B))

section Bernoulli

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def trialWeight (p : ℝ) (f : α → Bool) : ℝ :=
  ∏ i, if f i then p else 1 - p

def selected (f : α → Bool) : Finset α := univ.filter (fun i => f i)

lemma trialWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : α → Bool) :
    0 ≤ trialWeight p f := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> linarith

lemma sum_trialWeight (p : ℝ) : ∑ f : α → Bool, trialWeight p f = 1 := by
  unfold trialWeight
  rw [← Fintype.prod_sum (fun (_ : α) (b : Bool) => if b then p else 1 - p)]
  simp

lemma sum_trialWeight_contains (p : ℝ) (e : Finset α) :
    (∑ f : α → Bool, if e ⊆ selected f then trialWeight p f else 0) = p ^ e.card := by
  have hterm (f : α → Bool) :
      (if e ⊆ selected f then trialWeight p f else 0) =
        ∏ i, if i ∈ e then (if f i then p else 0) else (if f i then p else 1 - p) := by
    by_cases h : e ⊆ selected f
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hie : i ∈ e
      · have hf : f i = true := by simpa [selected] using h hie
        simp [hie, hf]
      · simp [hie]
    · rw [if_neg h]
      obtain ⟨i, hie, hi⟩ := Finset.not_subset.mp h
      have hf : f i = false := by simpa [selected] using hi
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hie, hf]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : α) (b : Bool) =>
    if i ∈ e then (if b then p else 0) else (if b then p else 1 - p))]
  simp [Fintype.sum_bool, Finset.prod_ite]

lemma sum_trialWeight_card (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f * ((selected f).card : ℝ)) = p * Fintype.card α := by
  calc
    _ = ∑ f : α → Bool, ∑ i : α,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [Finset.singleton_subset_iff, Finset.sum_ite_mem, mul_comm]
    _ = ∑ i : α, ∑ f : α → Bool,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = p * Fintype.card α := by
      simp_rw [sum_trialWeight_contains]
      simp [mul_comm]

lemma sum_trialWeight_edgeCount (p : ℝ) (H : Finset (Finset α)) :
    (∑ f : α → Bool, trialWeight p f * ((H.filter (· ⊆ selected f)).card : ℝ)) =
      ∑ e ∈ H, p ^ e.card := by
  calc
    _ = ∑ f : α → Bool, ∑ e ∈ H,
        if e ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.sum_filter, mul_comm]
    _ = ∑ e ∈ H, ∑ f : α → Bool,
        if e ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = ∑ e ∈ H, p ^ e.card := by simp_rw [sum_trialWeight_contains]

lemma alteration_bound (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B : Finset α, (∀ e ∈ H, ¬e ⊆ B) ∧
      p * Fintype.card α - (∑ e ∈ H, p ^ e.card) ≤ B.card := by
  let cost (f : α → Bool) : ℝ :=
    (selected f).card - (H.filter (· ⊆ selected f)).card
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image Finset.univ cost Finset.univ_nonempty
  have hexpect : p * Fintype.card α - (∑ e ∈ H, p ^ e.card) ≤ cost f := by
    have hle : (∑ g : α → Bool, trialWeight p g * cost g) ≤
        ∑ g : α → Bool, trialWeight p g * cost f := by
      apply Finset.sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g)
    simpa only [cost, mul_sub, Finset.sum_sub_distrib, sum_trialWeight_card,
      sum_trialWeight_edgeCount, ← Finset.sum_mul, sum_trialWeight, one_mul] using hle
  obtain ⟨B, hB, hcard, havoid⟩ := delete_forbidden_edges (selected f)
    (H.filter (· ⊆ selected f)) (fun e he => hH e (Finset.mem_filter.mp he).1)
  refine ⟨B, ?_, hexpect.trans ?_⟩
  · intro e he heB
    exact havoid e (Finset.mem_filter.mpr ⟨he, heB.trans hB⟩) heB
  · have hcard' : ((selected f).card : ℝ) ≤
        B.card + (H.filter (· ⊆ selected f)).card := by exact_mod_cast hcard
    dsimp [cost]
    linarith

end Bernoulli

noncomputable def sidonObstructions (A : Finset ℕ) : Finset (Finset A) := by
  classical
  exact Finset.univ.filter (fun e : Finset A =>
    ∃ a b c d : A, e = {a, b, c, d} ∧ a.val + c.val = b.val + d.val ∧
      ¬ ((a = b ∧ c = d) ∨ (a = d ∧ c = b)))

lemma sidonObstructions_nonempty (A : Finset ℕ) :
    ∀ e ∈ sidonObstructions A, e.Nonempty := by
  classical
  intro e he
  obtain ⟨_, a, b, c, d, rfl, _⟩ := Finset.mem_filter.mp he
  exact ⟨a, by simp⟩

lemma sidon_of_avoids_obstructions (A : Finset ℕ) (B : Finset A)
    (hB : ∀ e ∈ sidonObstructions A, ¬e ⊆ B) :
    IsSidon ((B.image (fun x : A => x.val) : Finset ℕ) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd heq
  simp only [Finset.mem_coe, Finset.mem_image] at ha hb hc hd
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  obtain ⟨c, hc, rfl⟩ := hc
  obtain ⟨d, hd, rfl⟩ := hd
  by_contra hn
  let E : Finset A := {a, b, c, d}
  have hEB : E ⊆ B := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hne : ¬ ((a = b ∧ c = d) ∨ (a = d ∧ c = b)) := by
    simpa only [Subtype.ext_iff] using hn
  exact hB E (Finset.mem_filter.mpr
    ⟨Finset.mem_univ E, a, b, c, d, rfl, heq, hne⟩) hEB

lemma sidon_alteration_bound (A : Finset ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * A.card - (∑ e ∈ sidonObstructions A, p ^ e.card) ≤
      (Finset.maxSidonSubsetCard A : ℝ) := by
  classical
  obtain ⟨B, hB, hcard⟩ := alteration_bound (sidonObstructions A)
    (sidonObstructions_nonempty A) p hp hp1
  have hsidon := sidon_of_avoids_obstructions A B hB
  have hsub : B.image (fun x : A => x.val) ⊆ A := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact a.property
  have hm : (B.image (fun x : A => x.val)).card ≤ Finset.maxSidonSubsetCard A :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsidon⟩)
  have hBi : (B.image (fun x : A => x.val)).card = B.card :=
    Finset.card_image_of_injective B Subtype.val_injective
  rw [hBi] at hm
  simpa using hcard.trans (by exact_mod_cast hm)


open Finset Filter

lemma divisor_card_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  let b : ℝ := 2 ^ δ
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + 1 / (b - 1)
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ 1 / (b - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcb : c * (b - 1) = b := by
    dsimp [c]
    field_simp [show b - 1 ≠ 0 by linarith]
    <;> ring
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ c * b ^ e := by
    have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ b) e
    calc
      (e : ℝ) + 1 ≤ c + (e : ℝ) * b := by
        nlinarith [mul_nonneg (Nat.cast_nonneg e) (le_of_lt (sub_pos.mpr hb))]
      _ = c * (1 + (e : ℝ) * (b - 1)) := by
        rw [mul_add, mul_one, ← mul_left_comm, hcb]
      _ ≤ c * b ^ e := mul_le_mul_of_nonneg_left hber hcpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ≥ K, (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    exact eventually_atTop.mp
      (tendsto_atTop.mp ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop) 2)
  refine ⟨c ^ K, pow_pos hcpos _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hδ.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p + 1 : ℕ) ≤
        (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpk : p < K
    · rw [if_pos hpk]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) = (n.factorization p : ℝ) + 1 := by push_cast; rfl
        _ ≤ c * b ^ n.factorization p := hsmall _
        _ ≤ c * ((p : ℝ) ^ δ) ^ n.factorization p := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpk, one_mul]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n.factorization p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p)))
        _ ≤ ((p : ℝ) ^ δ) ^ n.factorization p :=
          pow_le_pow_left₀ (by norm_num) (hK p (by omega)) _
  have hcoeff : (∏ p ∈ n.primeFactors, if p < K then c else 1) ≤ c ^ K := by
    have hcard : (n.primeFactors.filter (· < K)).card ≤ K := by
      calc
        _ ≤ (Finset.range K).card := Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = K := Finset.card_range K
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hc hcard
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    have hnprod' : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_pow_eq_self hn]
    exact_mod_cast hnprod'
  have hrpow : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p) = (n : ℝ) ^ δ := by
    calc
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ δ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
          ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm δ]
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ δ :=
        Real.finset_prod_rpow _ _ (by intros; positivity) _
      _ = (n : ℝ) ^ δ := by rw [hnprod]
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p :=
      Finset.prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < K then c else 1) * (n : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, hrpow]
    _ ≤ c ^ K * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg n) δ)


open Finset Filter

lemma difference_factor {x y D : ℕ} (hxy : y < x) (he : x ^ 2 = y ^ 2 + D) :
    D = (x - y) * (x + y) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hxy.le
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [he]

def squareDifferenceReps (N D : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun p => p.1 < p.2 ∧ p.2 ^ 2 = p.1 ^ 2 + D)

lemma squareDifferenceReps_card_le (N D : ℕ) (hD : 0 < D) :
    (squareDifferenceReps N D).card ≤ D.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1)
  · intro p hp
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2 + p.1, difference_factor hp.1 hp.2⟩, hD.ne'⟩
  · intro p hp q hq heq
    obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq⟩ := Finset.mem_filter.mp hq
    have hpF := difference_factor hp.1 hp.2
    have hqF := difference_factor hq.1 hq.2
    dsimp at heq
    rw [← heq] at hqF
    have hsum : p.2 + p.1 = q.2 + q.1 := by
      exact mul_left_cancel₀ (Nat.sub_pos_of_lt hp.1).ne' (hpF.symm.trans hqF)
    apply Prod.ext <;> omega

lemma squareDifferenceReps_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N D : ℕ, 0 < D → D ≤ N ^ 2 →
      ((squareDifferenceReps N D).card : ℝ) ≤ C * (N : ℝ) ^ (2 * δ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_subpower δ hδ
  refine ⟨C, hC, ?_⟩
  intro N D hD hDN
  have hDN' : (D : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hDN
  calc
    ((squareDifferenceReps N D).card : ℝ) ≤ (D.divisors.card : ℝ) := by
      exact_mod_cast squareDifferenceReps_card_le N D hD
    _ ≤ C * (D : ℝ) ^ δ := hbound D
    _ ≤ C * ((N : ℝ) ^ 2) ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg D) hDN' hδ.le) hC.le
    _ = C * (N : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      norm_num

def squareCollisions (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ ((Icc 1 N) ×ˢ (Icc 1 N))).filter
    (fun t => t.1.2 < t.1.1 ∧ t.1.1 ^ 2 + t.2.1 ^ 2 = t.1.2 ^ 2 + t.2.2 ^ 2)

lemma square_collision_fiber (N : ℕ) (p : ℕ × ℕ) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter
      (fun q => p.2 < p.1 ∧ p.1 ^ 2 + q.1 ^ 2 = p.2 ^ 2 + q.2 ^ 2)) =
    if p.2 < p.1 then squareDifferenceReps N (p.1 ^ 2 - p.2 ^ 2) else ∅ := by
  by_cases h : p.2 < p.1
  · have hsq : p.2 ^ 2 < p.1 ^ 2 := by nlinarith
    have hsub := Nat.sub_add_cancel hsq.le
    have hequiv (q : ℕ × ℕ) :
        p.1 ^ 2 + q.1 ^ 2 = p.2 ^ 2 + q.2 ^ 2 ↔
          q.1 < q.2 ∧ q.2 ^ 2 = q.1 ^ 2 + (p.1 ^ 2 - p.2 ^ 2) := by
      constructor
      · intro he
        constructor
        · nlinarith
        · omega
      · intro he
        omega
    ext q
    simp [h, squareDifferenceReps, hequiv]
  · simp [h]

lemma squareCollisions_card (N : ℕ) :
    (squareCollisions N).card = ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
      if p.2 < p.1 then (squareDifferenceReps N (p.1 ^ 2 - p.2 ^ 2)).card else 0 := by
  unfold squareCollisions
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.card_filter, square_collision_fiber]
  split <;> simp

lemma squareCollisions_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N : ℕ,
      ((squareCollisions N).card : ℝ) ≤ C * (N : ℝ) ^ (2 + 2 * δ) := by
  obtain ⟨C, hC, hrepr⟩ := squareDifferenceReps_subpower δ hδ
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN, squareCollisions, Real.zero_rpow (by linarith : (2 + 2 * δ) ≠ 0)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [squareCollisions_card, Nat.cast_sum]
  calc
    _ ≤ ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), C * (N : ℝ) ^ (2 * δ) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs with h
      · simp only [Finset.mem_product, Finset.mem_Icc] at hp
        have hD : 0 < p.1 ^ 2 - p.2 ^ 2 := Nat.sub_pos_of_lt (by nlinarith)
        have hDN : p.1 ^ 2 - p.2 ^ 2 ≤ N ^ 2 := by
          exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left hp.1.2 2)
        exact hrepr N _ hD hDN
      · simp only [Nat.cast_zero]
        positivity
    _ = C * (N : ℝ) ^ (2 + 2 * δ) := by
      simp only [Finset.sum_const, Finset.card_product, Nat.card_Icc,
        Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_mul]
      rw [Real.rpow_add hNpos]
      norm_num [Real.rpow_two]
      ring


open Finset Filter

lemma squareAP_parameters {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) :
    let y := c - b
    let d := 2 * b - (a + c)
    0 < y ∧ 0 < d ∧ a + y + d = b ∧ a + 2 * y + d = c ∧
      2 * y ^ 2 = d * (2 * a + d) := by
  dsimp only
  have hy : 0 < c - b := Nat.sub_pos_of_lt hbc
  have hyb : c - b + b = c := Nat.sub_add_cancel hbc.le
  have hac : a + c < 2 * b := by
    have he' : (a : ℤ) ^ 2 + (c : ℤ) ^ 2 = 2 * (b : ℤ) ^ 2 := by exact_mod_cast he
    have hpos : 0 < ((a : ℤ) - c) ^ 2 := sq_pos_of_ne_zero (by omega)
    by_contra! h
    have h' : 2 * (b : ℤ) ≤ (a : ℤ) + c := by exact_mod_cast h
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ 2 * b) h' 2
    nlinarith only [hs, he', hpos]
  have hd : 0 < 2 * b - (a + c) := Nat.sub_pos_of_lt hac
  have hdac := Nat.sub_add_cancel hac.le
  have hb : a + (c - b) + (2 * b - (a + c)) = b := by omega
  have hc : a + 2 * (c - b) + (2 * b - (a + c)) = c := by omega
  refine ⟨hy, hd, hb, hc, ?_⟩
  nth_rw 1 [← hb] at he
  nth_rw 1 [← hc] at he
  nlinarith only [he]

def squareAPs (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Icc 1 N) ×ˢ (Icc 1 N)) ×ˢ (Icc 1 N)).filter
    (fun t => t.1.1 < t.1.2 ∧ t.1.2 < t.2 ∧ t.1.1 ^ 2 + t.2 ^ 2 = 2 * t.1.2 ^ 2)

lemma squareAPs_card_le (N : ℕ) :
    (squareAPs N).card ≤ ∑ y ∈ Icc 1 N, (2 * y ^ 2).divisors.card := by
  let U : Finset (ℕ × ℕ) := (Icc 1 N).biUnion (fun y => {y} ×ˢ (2 * y ^ 2).divisors)
  have hU : U.card ≤ ∑ y ∈ Icc 1 N, (2 * y ^ 2).divisors.card := by
    exact Finset.card_biUnion_le.trans_eq (by simp)
  apply le_trans _ hU
  apply Finset.card_le_card_of_injOn (fun t : (ℕ × ℕ) × ℕ =>
    (t.2 - t.1.2, 2 * t.1.2 - (t.1.1 + t.2)))
  · intro t ht
    obtain ⟨hmem, hab, hbc, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
    apply Finset.mem_biUnion.mpr
    refine ⟨t.2 - t.1.2, ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc] at hmem
      exact Finset.mem_Icc.mpr ⟨hy, (Nat.sub_le _ _).trans hmem.2.2⟩
    · apply Finset.mem_product.mpr
      refine ⟨Finset.mem_singleton_self _, Nat.mem_divisors.mpr ?_⟩
      exact ⟨⟨2 * t.1.1 + (2 * t.1.2 - (t.1.1 + t.2)), hfac⟩, by positivity⟩
  · intro t ht u hu heq
    obtain ⟨_, hab, hbc, he⟩ := Finset.mem_filter.mp ht
    obtain ⟨_, hab', hbc', he'⟩ := Finset.mem_filter.mp hu
    obtain ⟨hy, hd, hb, hc, hfac⟩ := squareAP_parameters hab hbc he
    obtain ⟨hy', hd', hb', hc', hfac'⟩ := squareAP_parameters hab' hbc' he'
    have hyEq : t.2 - t.1.2 = u.2 - u.1.2 := congrArg Prod.fst heq
    have hdEq : 2 * t.1.2 - (t.1.1 + t.2) = 2 * u.1.2 - (u.1.1 + u.2) := congrArg Prod.snd heq
    rw [← hyEq, ← hdEq] at hfac'
    have haEq : 2 * t.1.1 + (2 * t.1.2 - (t.1.1 + t.2)) =
        2 * u.1.1 + (2 * t.1.2 - (t.1.1 + t.2)) :=
      mul_left_cancel₀ hd.ne' (hfac.symm.trans hfac')
    apply Prod.ext
    · apply Prod.ext <;> omega
    · omega

lemma squareAPs_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ N : ℕ,
      ((squareAPs N).card : ℝ) ≤ C * (N : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_subpower δ hδ
  refine ⟨C * 2 ^ δ, by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN, squareAPs, Real.zero_rpow (by linarith : 1 + 2 * δ ≠ 0)]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  calc
    ((squareAPs N).card : ℝ) ≤ ∑ y ∈ Icc 1 N, ((2 * y ^ 2).divisors.card : ℝ) := by
      exact_mod_cast squareAPs_card_le N
    _ ≤ ∑ y ∈ Icc 1 N, C * (2 * (N : ℝ) ^ 2) ^ δ := by
      apply Finset.sum_le_sum
      intro y hy
      have hyN : (y : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hy).2
      have hpow : (2 * y ^ 2 : ℕ) ≤ 2 * N ^ 2 := Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left (Finset.mem_Icc.mp hy).2 2)
      apply (hbound (2 * y ^ 2)).trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact_mod_cast hpow
    _ = (C * 2 ^ δ) * (N : ℝ) ^ (1 + 2 * δ) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg N), Real.rpow_add hNpos]
      norm_num
      ring


open Finset Filter

lemma nontrivial_sum_cross_ne {a b c d : ℕ} (he : a + c = b + d)
    (hn : ¬ ((a = b ∧ c = d) ∨ (a = d ∧ c = b))) :
    a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d := by omega

lemma sidonObstructions_card_either (A : Finset ℕ) (e : Finset A)
    (he : e ∈ sidonObstructions A) : e.card = 3 ∨ e.card = 4 := by
  classical
  obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
  have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
    simpa only [Subtype.ext_iff] using hn
  have hcross := nontrivial_sum_cross_ne he hn'
  have hab : a ≠ b := fun h => hcross.1 (congrArg Subtype.val h)
  have had : a ≠ d := fun h => hcross.2.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hcross.2.2.1 (congrArg Subtype.val h)
  have hcd : c ≠ d := fun h => hcross.2.2.2 (congrArg Subtype.val h)
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by
      intro h
      apply hab
      apply Subtype.ext
      have hv := congrArg Subtype.val h
      omega
    simp [hab, Ne.symm hab, had, hbd]
  · by_cases hbd : b = d
    · subst d
      simp [hab, hac, hcb, Ne.symm hcb]
    · simp [hab, hac, had, hbd, hcb, Ne.symm hcb, hcd]

def squaresBelow (N : ℕ) : Finset ℕ := (Icc 1 N).image (fun n => n ^ 2)

def squareAPSupport (t : (ℕ × ℕ) × ℕ) : Finset ℕ := {t.1.1 ^ 2, t.1.2 ^ 2, t.2 ^ 2}

def squareCollisionSupport (t : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ :=
  {t.1.1 ^ 2, t.1.2 ^ 2, t.2.1 ^ 2, t.2.2 ^ 2}

lemma support_of_squareAP_mem {N a b c : ℕ}
    (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (hc : c ∈ Icc 1 N)
    (he : a ^ 2 + c ^ 2 = 2 * b ^ 2) (hne : a ≠ c) :
    {a ^ 2, b ^ 2, c ^ 2} ∈ (squareAPs N).image squareAPSupport := by
  rcases lt_or_gt_of_ne hne with hac | hca
  · have hab : a < b := by nlinarith
    have hbc : b < c := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨((a, b), c), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩, hab, hbc, he⟩
  · have hcb : c < b := by nlinarith
    have hba : b < a := by nlinarith
    apply Finset.mem_image.mpr
    refine ⟨((c, b), a), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hc, hb⟩, ha⟩, hcb, hba, by simpa [add_comm] using he⟩
    · ext x
      simp [squareAPSupport, or_comm, or_left_comm, or_assoc]

lemma square_obstructions_four_bound (N : ℕ) :
    ((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4)).card ≤
      (squareCollisions N).card := by
  classical
  apply le_trans _ (Finset.card_image_le (f := squareCollisionSupport) (s := squareCollisions N))
  apply Finset.card_le_card_of_injOn (fun e : Finset (squaresBelow N) => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4) at he
    obtain ⟨he, _⟩ := Finset.mem_filter.mp he
    obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
    have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
      simpa only [Subtype.ext_iff] using hn
    have hab := (nontrivial_sum_cross_ne he hn').1
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
    obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp c.property
    obtain ⟨w, hw, hwd⟩ := Finset.mem_image.mp d.property
    have hxy : x ≠ y := by intro h; apply hab; rw [← hxa, ← hyb, h]
    have heq : x ^ 2 + z ^ 2 = y ^ 2 + w ^ 2 := by simpa [hxa, hyb, hzc, hwd] using he
    rcases lt_or_gt_of_ne hxy with hxy | hyx
    · apply Finset.mem_image.mpr
      refine ⟨((y, x), (w, z)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hy, hx⟩, Finset.mem_product.mpr ⟨hw, hz⟩⟩,
          hxy, heq.symm⟩
      · ext v
        simp [squareCollisionSupport, hxa, hyb, hzc, hwd, or_comm, or_left_comm, or_assoc]
    · apply Finset.mem_image.mpr
      refine ⟨((x, y), (z, w)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hx, hy⟩, Finset.mem_product.mpr ⟨hz, hw⟩⟩,
          hyx, heq⟩
      · simp [squareCollisionSupport, hxa, hyb, hzc, hwd]
  · exact (Finset.image_injective Subtype.val_injective).injOn

lemma square_obstructions_three_bound (N : ℕ) :
    ((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3)).card ≤
      (squareAPs N).card := by
  classical
  apply le_trans _ (Finset.card_image_le (f := squareAPSupport) (s := squareAPs N))
  apply Finset.card_le_card_of_injOn (fun e : Finset (squaresBelow N) => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3) at he
    obtain ⟨he, hecard⟩ := Finset.mem_filter.mp he
    obtain ⟨_, a, b, c, d, rfl, he, hn⟩ := Finset.mem_filter.mp he
    have hn' : ¬ ((a.val = b.val ∧ c.val = d.val) ∨ (a.val = d.val ∧ c.val = b.val)) := by
      simpa only [Subtype.ext_iff] using hn
    have hcross := nontrivial_sum_cross_ne he hn'
    have hab : a ≠ b := fun h => hcross.1 (congrArg Subtype.val h)
    have had : a ≠ d := fun h => hcross.2.1 (congrArg Subtype.val h)
    have hcb : c ≠ b := fun h => hcross.2.2.1 (congrArg Subtype.val h)
    have hcd : c ≠ d := fun h => hcross.2.2.2 (congrArg Subtype.val h)
    have hsame : a = c ∨ b = d := by
      by_cases hac : a = c
      · exact Or.inl hac
      by_cases hbd : b = d
      · exact Or.inr hbd
      have hfour : ({a, b, c, d} : Finset (squaresBelow N)).card = 4 := by
        simp [hab, hac, had, hbd, Ne.symm hcb, hcd]
      omega
    rcases hsame with hsame | hsame
    · subst c
      have hbd : b ≠ d := by
        intro h
        apply hab
        apply Subtype.ext
        have hv := congrArg Subtype.val h
        omega
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
      obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
      obtain ⟨w, hw, hwd⟩ := Finset.mem_image.mp d.property
      have hyw : y ≠ w := by
        intro h
        apply hbd
        apply Subtype.ext
        rw [← hyb, ← hwd, h]
      have heq : y ^ 2 + w ^ 2 = 2 * x ^ 2 := by rw [hyb, hwd, hxa]; omega
      have hAP := support_of_squareAP_mem hy hx hw heq hyw
      rw [hyb, hxa, hwd] at hAP
      convert hAP using 1 <;> ext v <;> simp [or_comm, or_left_comm, or_assoc]
    · subst d
      have hac : a ≠ c := by
        intro h
        apply hab
        apply Subtype.ext
        have hv := congrArg Subtype.val h
        omega
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
      obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp b.property
      obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp c.property
      have hxz : x ≠ z := by
        intro h
        apply hac
        apply Subtype.ext
        rw [← hxa, ← hzc, h]
      have heq : x ^ 2 + z ^ 2 = 2 * y ^ 2 := by rw [hxa, hzc, hyb]; omega
      have hAP := support_of_squareAP_mem hx hy hz heq hxz
      rw [hxa, hyb, hzc] at hAP
      convert hAP using 1 <;> ext v <;> simp [or_comm, or_left_comm, or_assoc]
  · exact (Finset.image_injective Subtype.val_injective).injOn

lemma obstruction_weight_sum (A : Finset ℕ) (p : ℝ) :
    (∑ e ∈ sidonObstructions A, p ^ e.card) =
      p ^ 3 * ((sidonObstructions A).filter (fun e => e.card = 3)).card +
      p ^ 4 * ((sidonObstructions A).filter (fun e => e.card = 4)).card := by
  classical
  calc
    _ = ∑ e ∈ sidonObstructions A,
        ((if e.card = 3 then p ^ 3 else 0) + (if e.card = 4 then p ^ 4 else 0)) := by
      apply Finset.sum_congr rfl
      intro e he
      rcases sidonObstructions_card_either A e he with h | h <;> simp [h]
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter, mul_comm]

lemma squaresBelow_card (N : ℕ) : (squaresBelow N).card = N := by
  unfold squaresBelow
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b hab
    nlinarith

lemma square_sidon_alteration (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * N - p ^ 3 * (squareAPs N).card - p ^ 4 * (squareCollisions N).card ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hm := sidon_alteration_bound (squaresBelow N) p hp hp1
  rw [squaresBelow_card, obstruction_weight_sum] at hm
  have h3 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 3)).card : ℝ) ≤
      (squareAPs N).card := by exact_mod_cast square_obstructions_three_bound N
  have h4 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card = 4)).card : ℝ) ≤
      (squareCollisions N).card := by exact_mod_cast square_obstructions_four_bound N
  have h3' := mul_le_mul_of_nonneg_left h3 (pow_nonneg hp 3)
  have h4' := mul_le_mul_of_nonneg_left h4 (pow_nonneg hp 4)
  linarith

lemma square_sidon_subpower_alteration (δ : ℝ) (hδ : 0 < δ) :
    ∃ C₃ > (0 : ℝ), ∃ C₄ > (0 : ℝ), ∀ (N : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 →
      p * N - (C₃ * (N : ℝ) ^ (1 + 2 * δ)) * p ^ 3 -
        (C₄ * (N : ℝ) ^ (2 + 2 * δ)) * p ^ 4 ≤
          (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  obtain ⟨C₃, hC₃, h3⟩ := squareAPs_subpower δ hδ
  obtain ⟨C₄, hC₄, h4⟩ := squareCollisions_subpower δ hδ
  refine ⟨C₃, hC₃, C₄, hC₄, ?_⟩
  intro N p hp hp1
  have hm := square_sidon_alteration N p hp hp1
  have h3' := mul_le_mul_of_nonneg_left (h3 N) (pow_nonneg hp 3)
  have h4' := mul_le_mul_of_nonneg_left (h4 N) (pow_nonneg hp 4)
  nlinarith only [hm, h3', h4']

lemma square_sidon_two_thirds (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (2 / 3 - 2 * η) ≤
      (Finset.maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  obtain ⟨C₃, hC₃, C₄, hC₄, hbound⟩ :=
    square_sidon_subpower_alteration (η / 2) (by positivity)
  have ht (C r : ℝ) (hr : 0 < r) :
      Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-r)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hr).comp tendsto_natCast_atTop_atTop).const_mul C
  have h3 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
    (ht C₃ (2 / 3 + η) (by linarith))
  have h4 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
    (ht C₄ (2 * η) (by positivity))
  have h0 := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) (ht 1 η hη)
  filter_upwards [h3, h4, h0, eventually_ge_atTop 1] with N h3 h4 h0 hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  let p : ℝ := (N : ℝ) ^ (-(1 / 3 + η))
  let S : ℝ := (N : ℝ) ^ (2 / 3 - η)
  have hp : 0 ≤ p := Real.rpow_nonneg hNpos.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hS : 0 ≤ S := Real.rpow_nonneg hNpos.le _
  have hmain := hbound N p hp hp1
  have hδ1 : (1 : ℝ) + 2 * (η / 2) = 1 + η := by ring
  have hδ2 : (2 : ℝ) + 2 * (η / 2) = 2 + η := by ring
  rw [hδ1, hδ2] at hmain
  have hPN : p * N = S := by
    dsimp [p, S]
    calc
      _ = (N : ℝ) ^ (-(1 / 3 + η)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (2 / 3 - η) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hm (C r s : ℝ) (k : ℕ) :
      (C * (N : ℝ) ^ r) * ((N : ℝ) ^ s) ^ k = C * (N : ℝ) ^ (r + s * k) := by
    rw [mul_assoc, ← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos]
  have he3 : (C₃ * (N : ℝ) ^ (1 + η)) * p ^ 3 =
      S * (C₃ * (N : ℝ) ^ (-(2 / 3 + η))) := by
    dsimp [p, S]
    rw [hm, mul_left_comm _ C₃, ← Real.rpow_add hNpos]
    congr 2
    norm_num
    ring
  have he4 : (C₄ * (N : ℝ) ^ (2 + η)) * p ^ 4 =
      S * (C₄ * (N : ℝ) ^ (-(2 * η))) := by
    dsimp [p, S]
    rw [hm, mul_left_comm _ C₄, ← Real.rpow_add hNpos]
    congr 2
    norm_num
    ring
  have he0 : (N : ℝ) ^ (2 / 3 - 2 * η) = S * (N : ℝ) ^ (-η) := by
    dsimp [S]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have h3' := mul_le_mul_of_nonneg_left h3 hS
  have h4' := mul_le_mul_of_nonneg_left h4 hS
  have h0' := mul_le_mul_of_nonneg_left h0 hS
  rw [hPN, he3, he4] at hmain
  rw [he0]
  nlinarith only [hmain, h3', h4', h0']

lemma conjecture_for_epsilon_gt_third (ε : ℝ) (hε : 1 / 3 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ) := by
  have h := square_sidon_two_thirds ((ε - 1 / 3) / 2) (by linarith)
  have he : (2 : ℝ) / 3 - 2 * ((ε - 1 / 3) / 2) = 1 - ε := by ring
  simpa only [he, squaresBelow] using h


/-
## Complementary elementary upper bound

The modular bound below implies that the maximum Sidon-subset size is `o(N)`.
It uses the Chinese remainder theorem, not analytic estimates for primes.
This upper bound does not settle the conjectured `N^(1-o(1))` lower bound.
-/

open Finset

lemma congruent_pair_quotient_injective {A : Finset ℕ} (hs : IsSidon (A : Set ℕ))
    (q : ℕ) {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hmab : a % q = b % q) (hmcd : c % q = d % q)
    (he : ((a / q : ℕ) : ℤ) - (b / q : ℕ) = ((c / q : ℕ) : ℤ) - (d / q : ℕ)) :
    a = c ∧ b = d := by
  have hquot : a / q + d / q = c / q + b / q := by omega
  have hmul := congrArg (fun n : ℕ => q * n) hquot
  simp only [mul_add] at hmul
  have has := Nat.mod_add_div a q
  have hbs := Nat.mod_add_div b q
  have hcs := Nat.mod_add_div c q
  have hds := Nat.mod_add_div d q
  have heq : a + d = c + b := by omega
  rcases hs a ha c hc d hd b hb heq with h | h
  · exact ⟨h.1, h.2.symm⟩
  · exact (hab h.1).elim

lemma congruent_pairs_card_bound {A : Finset ℕ} {L : ℕ}
    (hs : IsSidon (A : Set ℕ)) (hL : ∀ a ∈ A, a ≤ L) (q : ℕ) :
    ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card ≤
      A.card + 2 * (L / q) + 1 := by
  let f : ℕ × ℕ → ℕ ⊕ ℤ := fun p =>
    if p.1 = p.2 then Sum.inl p.1 else
      Sum.inr ((p.1 / q : ℕ) - ((p.2 / q : ℕ) : ℤ))
  have hh : ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card ≤
      (A.disjSum (Icc (-((L / q : ℕ) : ℤ)) ((L / q : ℕ) : ℤ))).card := by
    apply Finset.card_le_card_of_injOn f
    · rintro ⟨a,b⟩ hp
      obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      dsimp [f]
      split_ifs with he
      · simp [ha]
      · have haL := Nat.div_le_div_right (hL a ha) (c := q)
        have hbL := Nat.div_le_div_right (hL b hb) (c := q)
        apply Finset.mem_disjSum.mpr
        right
        refine ⟨_, ?_, rfl⟩
        apply mem_Icc.mpr
        have ha0 : 0 ≤ (a : ℤ) / q := Int.ediv_nonneg (by omega) (by omega)
        have hb0 : 0 ≤ (b : ℤ) / q := Int.ediv_nonneg (by omega) (by omega)
        constructor <;> omega
    · rintro ⟨a,b⟩ hp ⟨c,d⟩ hr he
      obtain ⟨hp, hmab⟩ := Finset.mem_filter.mp hp
      obtain ⟨hr, hmcd⟩ := Finset.mem_filter.mp hr
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hc, hd⟩ := Finset.mem_product.mp hr
      dsimp [f] at he
      split_ifs at he with hab hcd hcd
      · simp only [Sum.inl.injEq] at he
        exact Prod.ext he (by omega)
      · have he' := Sum.inr.inj he
        have hpair := congruent_pair_quotient_injective hs q ha hb hc hd hab hmab hmcd he'
        exact Prod.ext hpair.1 hpair.2
  rw [card_disjSum, Int.card_Icc] at hh
  have hcard : (((L / q : ℕ) : ℤ) + 1 - -((L / q : ℕ) : ℤ)).toNat = 2 * (L / q) + 1 := by omega
  rw [hcard] at hh
  omega

lemma card_sq_le_residue_count_mul_pairs (A C : Finset ℕ) (q : ℕ)
    (hC : ∀ a ∈ A, a % q ∈ C) :
    A.card ^ 2 ≤ C.card *
      ((A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)).card := by
  let F := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 % q = p.2 % q)
  have hsum : A.card = ∑ r ∈ C, (A.filter (fun a => a % q = r)).card :=
    Finset.card_eq_sum_card_fiberwise hC
  have hsum2 : F.card = ∑ r ∈ C, (A.filter (fun a => a % q = r)).card ^ 2 := by
    have hm : Set.MapsTo (fun p : ℕ × ℕ => p.1 % q) (F : Set (ℕ × ℕ)) C := by
      intro p hp
      exact hC p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    rw [Finset.card_eq_sum_card_fiberwise hm]
    apply Finset.sum_congr rfl
    intro r hr
    have hf : F.filter (fun p => p.1 % q = r) =
        (A.filter (fun a => a % q = r)) ×ˢ (A.filter (fun a => a % q = r)) := by
      ext p
      simp only [F, mem_filter, mem_product]
      aesop
    rw [hf, card_product, pow_two]
  change A.card ^ 2 ≤ C.card * F.card
  rw [hsum2, hsum]
  exact sq_sum_le_card_mul_sum_sq

lemma sidon_modular_card_bound {A C : Finset ℕ} {L q : ℕ}
    (hs : IsSidon (A : Set ℕ)) (hL : ∀ a ∈ A, a ≤ L)
    (hC : ∀ a ∈ A, a % q ∈ C) :
    A.card ^ 2 ≤ C.card * (A.card + 2 * (L / q) + 1) := by
  exact (card_sq_le_residue_count_mul_pairs A C q hC).trans
    (Nat.mul_le_mul_left C.card (congruent_pairs_card_bound hs hL q))


open Finset Filter
open scoped Topology

noncomputable def quadraticResidues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.image (fun a : ZMod q => a ^ 2)

lemma mem_quadraticResidues {q : ℕ} [NeZero q] (r : ZMod q) :
    r ∈ quadraticResidues q ↔ ∃ a : ZMod q, a ^ 2 = r := by
  simp [quadraticResidues]

lemma quadraticResidues_card_le (q : ℕ) [NeZero q] :
    (quadraticResidues q).card ≤ q / 2 + 1 := by
  let T := (range (q / 2 + 1)).image (fun a : ℕ => (a : ZMod q) ^ 2)
  have hsub : quadraticResidues q ⊆ T := by
    intro r hr
    obtain ⟨a, rfl⟩ := (mem_quadraticResidues r).mp hr
    by_cases ha : a.val ≤ q / 2
    · exact mem_image.mpr ⟨a.val, mem_range.mpr (by omega), by simp⟩
    · have ha' := ZMod.val_lt a
      refine mem_image.mpr ⟨q - a.val, mem_range.mpr (by omega), ?_⟩
      have he : ((q - a.val : ℕ) : ZMod q) = -a := by
        rw [Nat.cast_sub ha'.le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
      rw [he, neg_sq]
  exact (card_le_card hsub).trans
    ((card_image_le (s := range (q / 2 + 1)) (f := fun a : ℕ => (a : ZMod q) ^ 2)).trans_eq
      (card_range _))

lemma quadraticResidues_card_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    (quadraticResidues (m * n)).card ≤
      (quadraticResidues m).card * (quadraticResidues n).card := by
  rw [← card_product]
  apply card_le_card_of_injOn (ZMod.chineseRemainder hc)
  · intro r hr
    obtain ⟨a, rfl⟩ := (mem_quadraticResidues r).mp hr
    rw [map_pow]
    exact mem_product.mpr ⟨(mem_quadraticResidues _).mpr
      ⟨(ZMod.chineseRemainder hc a).1, rfl⟩,
      (mem_quadraticResidues _).mpr ⟨(ZMod.chineseRemainder hc a).2, rfl⟩⟩
  · exact fun _ _ _ _ h => (ZMod.chineseRemainder hc).injective h

noncomputable def quadraticResidueDensity (q : ℕ) : ℝ :=
  if h : q = 0 then 1 else
    letI : NeZero q := ⟨h⟩
    (quadraticResidues q).card / (q : ℝ)

lemma quadraticResidueDensity_eq (q : ℕ) [NeZero q] :
    quadraticResidueDensity q = (quadraticResidues q).card / (q : ℝ) := by
  simp [quadraticResidueDensity, NeZero.ne q]

lemma quadraticResidueDensity_nonneg (q : ℕ) : 0 ≤ quadraticResidueDensity q := by
  unfold quadraticResidueDensity
  split <;> positivity

lemma quadraticResidueDensity_le_one (q : ℕ) [NeZero q] :
    quadraticResidueDensity q ≤ 1 := by
  rw [quadraticResidueDensity_eq]
  apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))).mpr
  exact_mod_cast (by simpa using card_le_univ (quadraticResidues q) :
    (quadraticResidues q).card ≤ q)

lemma quadraticResidueDensity_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    quadraticResidueDensity (m * n) ≤
      quadraticResidueDensity m * quadraticResidueDensity n := by
  simp only [quadraticResidueDensity_eq, Nat.cast_mul, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (by exact_mod_cast quadraticResidues_card_mul_le m n hc)
    (by positivity)

lemma quadraticResidueDensity_le_three_quarters (q : ℕ) (hq : 4 ≤ q) :
    quadraticResidueDensity q ≤ 3 / 4 := by
  letI : NeZero q := ⟨by omega⟩
  rw [quadraticResidueDensity_eq]
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < q by omega))).mpr
  have hc : ((quadraticResidues q).card : ℝ) ≤ (q / 2 : ℕ) + 1 := by
    exact_mod_cast quadraticResidues_card_le q
  have hd : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := by
    exact_mod_cast (Nat.cast_div_le (m := q) (n := 2) (α := ℝ))
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  linarith

lemma exists_small_quadraticResidueDensity (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ, 0 < Q ∧ quadraticResidueDensity Q < δ := by
  have hconstruct (k : ℕ) : ∃ Q : ℕ, 0 < Q ∧
      quadraticResidueDensity Q ≤ (3 / 4 : ℝ) ^ k := by
    induction k with
    | zero => exact ⟨1, by omega, by simpa using quadraticResidueDensity_le_one 1⟩
    | succ k ih =>
      obtain ⟨Q, hQ, hd⟩ := ih
      letI : NeZero Q := ⟨hQ.ne'⟩
      letI : NeZero (4 * Q + 1) := ⟨by omega⟩
      have hc : Q.Coprime (4 * Q + 1) := by
        simp [Nat.coprime_mul_right_add_right]
      refine ⟨Q * (4 * Q + 1), by positivity, ?_⟩
      calc
        _ ≤ quadraticResidueDensity Q * quadraticResidueDensity (4 * Q + 1) :=
          quadraticResidueDensity_mul_le _ _ hc
        _ ≤ (3 / 4 : ℝ) ^ k * (3 / 4) :=
          mul_le_mul hd (quadraticResidueDensity_le_three_quarters _ (by omega))
            (quadraticResidueDensity_nonneg _) (by positivity)
        _ = _ := (pow_succ _ _).symm
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨k, hk⟩ := ((ht.eventually (gt_mem_nhds hδ)).exists)
  obtain ⟨Q, hQ, hd⟩ := hconstruct k
  exact ⟨Q, hQ, hd.trans_lt hk⟩

lemma square_sidon_modular_card_bound {A : Finset ℕ} {N Q : ℕ} [NeZero Q]
    (hA : A ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2))
    (hs : IsSidon (A : Set ℕ)) :
    A.card ^ 2 ≤ (quadraticResidues Q).card * (A.card + 2 * (N ^ 2 / Q) + 1) := by
  let C := (quadraticResidues Q).image ZMod.val
  have hc : C.card = (quadraticResidues Q).card :=
    card_image_iff.mpr (fun _ _ _ _ h => ZMod.val_injective Q h)
  rw [← hc]
  apply sidon_modular_card_bound hs
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp (hA ha)
    exact Nat.pow_le_pow_left (mem_Icc.mp hn).2 2
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp (hA ha)
    refine mem_image.mpr ⟨(n : ZMod Q) ^ 2, (mem_quadraticResidues _).mpr ⟨n, rfl⟩, ?_⟩
    rw [← Nat.cast_pow, ZMod.val_natCast]

lemma max_square_sidon_modular_card_bound (N Q : ℕ) [NeZero Q] :
    let M := Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))
    M ^ 2 ≤ (quadraticResidues Q).card * (M + 2 * (N ^ 2 / Q) + 1) := by
  classical
  let S := (Icc 1 N).image (fun n : ℕ => n ^ 2)
  have hne : (S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨by simp, ?_⟩⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, he⟩ := exists_mem_eq_sup _ hne Finset.card
  have hA' := mem_filter.mp hA
  change ((S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).sup
    Finset.card) ^ 2 ≤ _ * (((S.powerset.filter (fun A : Finset ℕ =>
      IsSidon (A : Set ℕ))).sup Finset.card) + 2 * (N ^ 2 / Q) + 1)
  rw [he]
  exact square_sidon_modular_card_bound (mem_powerset.mp hA'.1) hA'.2

lemma max_square_sidon_card_le (N : ℕ) :
    Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) ≤ N := by
  classical
  unfold Finset.maxSidonSubsetCard
  apply Finset.sup_le
  intro A hA
  have hsub := mem_powerset.mp (mem_filter.mp hA).1
  exact (card_le_card hsub).trans (by simpa using
    (card_image_le (s := Icc 1 N) (f := fun n : ℕ => n ^ 2)))

lemma max_square_sidon_real_modular_bound (N Q : ℕ) [NeZero Q] :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ^ 2 ≤
      2 * quadraticResidueDensity Q * (N : ℝ) ^ 2 +
        (quadraticResidues Q).card * ((N : ℝ) + 1) := by
  let M := Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2))
  have hb : (M : ℝ) ^ 2 ≤ (quadraticResidues Q).card *
      ((M : ℝ) + 2 * ((N ^ 2 / Q : ℕ) : ℝ) + 1) := by
    exact_mod_cast max_square_sidon_modular_card_bound N Q
  have hm : (M : ℝ) ≤ N := by exact_mod_cast max_square_sidon_card_le N
  have hd : ((N ^ 2 / Q : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / Q := by
    apply (le_div_iff₀ (show (0 : ℝ) < Q by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q))).mpr
    exact_mod_cast Nat.div_mul_le_self (N ^ 2) Q
  have h := mul_le_mul_of_nonneg_left (show
      (M : ℝ) + 2 * ((N ^ 2 / Q : ℕ) : ℝ) + 1 ≤
        N + 2 * ((N : ℝ) ^ 2 / Q) + 1 by linarith)
    (Nat.cast_nonneg (α := ℝ) (quadraticResidues Q).card)
  rw [quadraticResidueDensity_eq]
  change (M : ℝ) ^ 2 ≤ _
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

lemma square_sidon_elementary_eventually_small_linear (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
        δ * N := by
  obtain ⟨Q, hQ, hsmall⟩ := exists_small_quadraticResidueDensity (δ ^ 2 / 4) (by positivity)
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hNlim : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNlim.eventually (eventually_ge_atTop (1 : ℝ)),
    hNlim.eventually (eventually_ge_atTop
      (4 * ((quadraticResidues Q).card : ℝ) / δ ^ 2))] with N hN1 hNc
  have hmain := max_square_sidon_real_modular_bound N Q
  have hsmall' : 2 * quadraticResidueDensity Q ≤ δ ^ 2 / 2 := by linarith
  have hsmallN := mul_le_mul_of_nonneg_right hsmall' (sq_nonneg (N : ℝ))
  have hNc' := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hNc
  have hNcN := mul_le_mul_of_nonneg_right hNc' (Nat.cast_nonneg (α := ℝ) N)
  have hsN := mul_le_mul_of_nonneg_left hN1
    (Nat.cast_nonneg (α := ℝ) (quadraticResidues Q).card)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hδ.le (Nat.cast_nonneg N))).mp
  nlinarith

lemma square_sidon_elementary_density_zero :
    Tendsto (fun N : ℕ =>
      (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) / N)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [square_sidon_elementary_eventually_small_linear (ε / 2) (by positivity),
    eventually_ge_atTop 1] with N hN hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt ((div_le_iff₀ hNp).mpr hN)
  linarith



lemma square_sidon_density_zero :
    Tendsto (fun N : ℕ =>
      (Finset.maxSidonSubsetCard
        ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) / N) atTop (𝓝 0) :=
  square_sidon_elementary_density_zero

/-
## Quantitative upper bound

For N ≥ 512 the maximum cardinality is at most
  4 * N * exp (-sqrt (log N) / 8).
The exponent loss still tends to zero, so this does not disprove Erdős 773.
-/

open Finset

noncomputable def dyadicSievePrime (i : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (2 ^ (i + 2)) (by positivity)).choose

lemma dyadicSievePrime_spec (i : ℕ) :
    (dyadicSievePrime i).Prime ∧ 2 ^ (i + 2) < dyadicSievePrime i ∧
      dyadicSievePrime i ≤ 2 ^ (i + 3) := by
  have h := (Nat.exists_prime_lt_and_le_two_mul (2 ^ (i + 2)) (by positivity)).choose_spec
  refine ⟨h.1, h.2.1, ?_⟩
  simpa [dyadicSievePrime, show i + 3 = (i + 2) + 1 by omega, pow_succ, mul_comm]
    using h.2.2

lemma dyadicSievePrime_strictMono : StrictMono dyadicSievePrime := by
  intro i j hij
  exact ((dyadicSievePrime_spec i).2.2.trans
    (Nat.pow_le_pow_right (by omega) (show i + 3 ≤ j + 2 by omega))).trans_lt
      (dyadicSievePrime_spec j).2.1

noncomputable def dyadicSieveModulus (k : ℕ) : ℕ :=
  ∏ i ∈ range k, dyadicSievePrime i

lemma dyadicSieveModulus_pos (k : ℕ) : 0 < dyadicSieveModulus k := by
  exact Finset.prod_pos (fun i hi => (dyadicSievePrime_spec i).1.pos)

lemma dyadicSieveModulus_le (k : ℕ) : dyadicSieveModulus k ≤ 2 ^ (k + 2) ^ 2 := by
  calc
    _ ≤ ∏ i ∈ range k, (2 : ℕ) ^ (k + 2) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      exact (dyadicSievePrime_spec i).2.2.trans
        (Nat.pow_le_pow_right (by omega) (show i + 3 ≤ k + 2 by simpa using hi))
    _ = 2 ^ ((k + 2) * k) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma dyadicSieveModulus_density (k : ℕ) :
    quadraticResidueDensity (dyadicSieveModulus k) ≤ (3 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simpa [dyadicSieveModulus] using quadraticResidueDensity_le_one 1
  | succ k ih =>
    letI : NeZero (dyadicSieveModulus k) := ⟨(dyadicSieveModulus_pos k).ne'⟩
    letI : NeZero (dyadicSievePrime k) := ⟨(dyadicSievePrime_spec k).1.ne_zero⟩
    have hc : (dyadicSieveModulus k).Coprime (dyadicSievePrime k) := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.prod_right
      intro i hi
      apply ((dyadicSievePrime_spec k).1.coprime_iff_not_dvd).mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq (dyadicSievePrime_spec k).1
        (dyadicSievePrime_spec i).1).mp hd
      exact (Nat.ne_of_gt (dyadicSievePrime_strictMono (mem_range.mp hi))) he
    have hp4 : 4 ≤ dyadicSievePrime k := by
      have hp := (dyadicSievePrime_spec k).2.1
      have h4 : (4 : ℕ) ≤ 2 ^ (k + 2) := by
        simpa using (Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ k + 2 by omega))
      omega
    change quadraticResidueDensity (∏ i ∈ range (k + 1), dyadicSievePrime i) ≤ _
    rw [prod_range_succ]
    calc
      _ ≤ quadraticResidueDensity (dyadicSieveModulus k) *
          quadraticResidueDensity (dyadicSievePrime k) := quadraticResidueDensity_mul_le _ _ hc
      _ ≤ (3 / 4 : ℝ) ^ k * (3 / 4) :=
        mul_le_mul ih (quadraticResidueDensity_le_three_quarters _ hp4)
          (quadraticResidueDensity_nonneg _) (by positivity)
      _ = _ := (pow_succ _ _).symm

lemma square_sidon_quantitative_upper_sq (k N : ℕ) (hN : 2 ^ (k + 3) ^ 2 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ^ 2 ≤
      4 * (3 / 4 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  let Q := dyadicSieveModulus k
  letI : NeZero Q := ⟨(dyadicSieveModulus_pos k).ne'⟩
  have hQN : 2 ^ k * Q ≤ N := by
    calc
      _ ≤ 2 ^ k * 2 ^ (k + 2) ^ 2 := Nat.mul_le_mul_left _ (dyadicSieveModulus_le k)
      _ = 2 ^ (k + (k + 2) ^ 2) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (k + 3) ^ 2 := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ ≤ N := hN
  have hQN' : (2 : ℝ) ^ k * Q ≤ N := by exact_mod_cast hQN
  have hhalf := mul_le_mul_of_nonneg_left hQN' (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)
  have he : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, he, one_mul] at hhalf
  have hhalf34 : (1 / 2 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hQr : (Q : ℝ) ≤ (3 / 4 : ℝ) ^ k * N :=
    hhalf.trans (mul_le_mul_of_nonneg_right hhalf34 (Nat.cast_nonneg N))
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast ((Nat.one_le_pow _ _ (by omega : 0 < (2 : ℕ))).trans hN)
  have hs : ((quadraticResidues Q).card : ℝ) ≤ Q := by
    exact_mod_cast (by simpa using card_le_univ (quadraticResidues Q) :
      (quadraticResidues Q).card ≤ Q)
  have ht := mul_le_mul (hs.trans hQr) (show (N : ℝ) + 1 ≤ 2 * N by linarith)
    (by positivity : (0 : ℝ) ≤ N + 1) (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k * N)
  have hd := mul_le_mul_of_nonneg_right (dyadicSieveModulus_density k)
    (show (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2 by positivity)
  have hb := max_square_sidon_real_modular_bound N Q
  change quadraticResidueDensity Q * (2 * (N : ℝ) ^ 2) ≤ _ at hd
  nlinarith

lemma square_sidon_quantitative_upper (k N : ℕ) (hN : 2 ^ (k + 3) ^ 2 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := by
  have h := square_sidon_quantitative_upper_sq k N hN
  have hs : ((Real.sqrt (3 / 4) : ℝ) ^ k) ^ 2 = (3 / 4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
  nlinarith

lemma square_sidon_stretched_exponential_upper (N : ℕ) (hN : 512 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      4 * N * Real.exp (-Real.sqrt (Real.log N) / 8) := by
  let l := Nat.log 2 N
  let t := Nat.sqrt l
  let k := t - 3
  have hNp : 0 < N := by omega
  have hNp' : (0 : ℝ) < N := by exact_mod_cast hNp
  have hl9 : 9 ≤ l := Nat.le_log_of_pow_le (by omega) (by norm_num; exact hN)
  have ht3 : 3 ≤ t := Nat.le_sqrt.mpr (by norm_num; exact hl9)
  have hk : k + 3 = t := Nat.sub_add_cancel ht3
  have ht2 : t ^ 2 ≤ l := by simpa only [pow_two] using Nat.sqrt_le l
  have hpow : 2 ^ (k + 3) ^ 2 ≤ N := by
    rw [hk]
    exact (Nat.pow_le_pow_right (by omega) ht2).trans (Nat.pow_log_le_self 2 hNp.ne')
  have hlupper : l + 1 ≤ (t + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt l
    change l < (t + 1) * (t + 1) at h
    nlinarith
  have hNupper : N ≤ 2 ^ (t + 1) ^ 2 :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) N).le.trans
      (Nat.pow_le_pow_right (by omega) hlupper)
  have hln : Real.log N ≤ ((t : ℝ) + 1) ^ 2 := by
    have hn : (N : ℝ) ≤ (2 : ℝ) ^ (t + 1) ^ 2 := by exact_mod_cast hNupper
    have h := Real.log_le_log hNp' hn
    rw [Real.log_pow] at h
    have h2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hh := mul_le_mul_of_nonneg_left h2
      (Nat.cast_nonneg (α := ℝ) ((t + 1) ^ 2))
    push_cast at h hh
    nlinarith
  have hsqrt : Real.sqrt (Real.log N) ≤ (k : ℝ) + 4 := by
    have h := (Real.sqrt_le_iff).mpr ⟨by positivity, hln⟩
    have hk' : (k : ℝ) + 3 = t := by exact_mod_cast hk
    linarith
  have hrlog : Real.log (Real.sqrt (3 / 4)) ≤ -(1 / 8 : ℝ) := by
    rw [Real.log_sqrt (by norm_num)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    linarith
  have hrpow : (Real.sqrt (3 / 4) : ℝ) ^ k ≤ Real.exp (-(k : ℝ) / 8) := by
    calc
      _ = Real.exp ((k : ℝ) * Real.log (Real.sqrt (3 / 4))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_left hrlog (Nat.cast_nonneg (α := ℝ) k)
        linarith)
  have he : Real.exp (-(k : ℝ) / 8) ≤
      Real.exp (1 / 2) * Real.exp (-Real.sqrt (Real.log N) / 8) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) using 1 <;> norm_num
  have hfinal : (Real.sqrt (3 / 4) : ℝ) ^ k ≤
      2 * Real.exp (-Real.sqrt (Real.log N) / 8) :=
    hrpow.trans (he.trans (mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)))
  have hh := mul_le_mul_of_nonneg_right hfinal (show (0 : ℝ) ≤ 2 * N by positivity)
  have hm := square_sidon_quantitative_upper k N hpow
  nlinarith


open Finset

set_option maxHeartbeats 1000000

def sievePrimes (n : ℕ) : Finset ℕ :=
  (range (2 * n + 1)).filter (fun p => p.Prime ∧ 5 ≤ p)

def sievePrimorial (n : ℕ) : ℕ := ∏ p ∈ sievePrimes n, p

lemma sievePrimorial_pos (n : ℕ) : 0 < sievePrimorial n := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_filter.mp hp).2.1.pos

lemma sievePrimorial_le (n : ℕ) : sievePrimorial n ≤ 4 ^ (2 * n) := by
  have hs : sievePrimes n ⊆ (range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.1⟩
  calc
    _ ≤ primorial (2 * n) := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hs
      intro p hp _
      exact (mem_filter.mp hp).2.one_lt.le
    _ ≤ _ := primorial_le_4_pow _

lemma sievePrimes_card_le (n : ℕ) : (sievePrimes n).card ≤ 2 * n + 1 := by
  simpa using (card_filter_le (s := range (2 * n + 1))
    (p := fun p => p.Prime ∧ 5 ≤ p))

lemma centralBinom_two_pow_le (n : ℕ) : 2 ^ n ≤ Nat.centralBinom n := by
  by_cases hn : 4 ≤ n
  · have h := Nat.four_pow_lt_mul_centralBinom n hn
    have hn2 : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
    have he : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    rw [he] at h
    have hpos : 0 < (2 : ℕ) ^ n := by positivity
    nlinarith
  · interval_cases n <;> decide

lemma centralBinom_le_prime_count_pow (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤
      (2 * n) ^ ((range (2 * n + 1)).filter Nat.Prime).card := by
  have he : (∏ p ∈ (range (2 * n + 1)).filter Nat.Prime,
      p ^ (Nat.centralBinom n).factorization p) = Nat.centralBinom n := by
    rw [Finset.prod_filter_of_ne]
    · exact Nat.prod_pow_factorization_centralBinom n
    · intro p _ hp
      by_contra h
      simp [Nat.factorization_eq_zero_of_not_prime _ h] at hp
  rw [← he]
  calc
    _ ≤ ∏ _p ∈ (range (2 * n + 1)).filter Nat.Prime, (2 * n) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    _ = _ := by simp

lemma sievePrimes_card_covers_prime_count (n : ℕ) :
    ((range (2 * n + 1)).filter Nat.Prime).card ≤ (sievePrimes n).card + 2 := by
  have hs : (range (2 * n + 1)).filter Nat.Prime ⊆ sievePrimes n ∪ {2, 3} := by
    intro p hp
    by_cases h5 : 5 ≤ p
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hp).1,
        (mem_filter.mp hp).2, h5⟩)
    · have hprime := (mem_filter.mp hp).2
      have hp2 : 2 ≤ p := hprime.two_le
      have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hprime
      have : p = 2 ∨ p = 3 := by omega
      exact mem_union_right _ (by simpa using this)
  exact (card_le_card hs).trans (by
    have h := card_union_le (sievePrimes n) {2, 3}
    simpa using h)

lemma sievePrimes_card_log_lower (n : ℕ) (hn : 128 ≤ n) :
    (n : ℝ) / 8 ≤ (sievePrimes n).card * Real.log n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog128 : Real.log 128 ≤ 7 := by
    have he : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hnlog : Real.log n ≤ (n : ℝ) / 16 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnp (by norm_num : (0 : ℝ) < 128))
    rw [Real.log_div hnp.ne' (by norm_num : (128 : ℝ) ≠ 0)] at h
    linarith
  have hlogn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpow : (2 : ℕ) ^ n ≤ (2 * n) ^ ((sievePrimes n).card + 2) :=
    (centralBinom_two_pow_le n).trans ((centralBinom_le_prime_count_pow n (by omega)).trans
      (Nat.pow_le_pow_right (by omega) (sievePrimes_card_covers_prime_count n)))
  have hpowR : (2 : ℝ) ^ n ≤ (2 * (n : ℝ)) ^ ((sievePrimes n).card + 2) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) hpowR
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnp.ne'] at hl
  push_cast at hl
  have h1 := mul_le_mul_of_nonneg_left hlog2 hnp.le
  have h2 := mul_le_mul_of_nonneg_left hlogn2
    (show (0 : ℝ) ≤ (sievePrimes n).card + 2 by positivity)
  nlinarith

lemma quadraticResidueDensity_prod_primes (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    quadraticResidueDensity (∏ p ∈ S, p) ≤ (3 / 4 : ℝ) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using quadraticResidueDensity_le_one 1
  | @insert p S hp ih =>
    have hp' := hS p (mem_insert_self _ _)
    have hS' : ∀ q ∈ S, q.Prime ∧ 5 ≤ q :=
      fun q hq => hS q (mem_insert_of_mem hq)
    letI : NeZero p := ⟨hp'.1.ne_zero⟩
    letI : NeZero (∏ q ∈ S, q) := ⟨(Finset.prod_pos
      (fun q hq => (hS' q hq).1.pos)).ne'⟩
    have hc : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (hp'.1.coprime_iff_not_dvd).mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hp'.1 (hS' q hq).1).mp hd
      exact hp (he ▸ hq)
    rw [prod_insert hp, card_insert_of_notMem hp, pow_succ]
    calc
      _ ≤ quadraticResidueDensity p * quadraticResidueDensity (∏ q ∈ S, q) :=
        quadraticResidueDensity_mul_le _ _ hc
      _ ≤ (3 / 4 : ℝ) * (3 / 4 : ℝ) ^ S.card :=
        mul_le_mul (quadraticResidueDensity_le_three_quarters _ (by omega)) (ih hS')
          (quadraticResidueDensity_nonneg _) (by norm_num)
      _ = _ := by ring

lemma sievePrimorial_density (n : ℕ) :
    quadraticResidueDensity (sievePrimorial n) ≤ (3 / 4 : ℝ) ^ (sievePrimes n).card :=
  quadraticResidueDensity_prod_primes _ (fun _ hp => (mem_filter.mp hp).2)

lemma square_sidon_upper_of_modulus (k N Q : ℕ) (hQ : 0 < Q)
    (hQN : 2 ^ k * Q ≤ N) (hd : quadraticResidueDensity Q ≤ (3 / 4 : ℝ) ^ k) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hQN' : (2 : ℝ) ^ k * Q ≤ N := by exact_mod_cast hQN
  have hhalf := mul_le_mul_of_nonneg_left hQN' (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)
  have he : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, he, one_mul] at hhalf
  have hhalf34 : (1 / 2 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hQr : (Q : ℝ) ≤ (3 / 4 : ℝ) ^ k * N :=
    hhalf.trans (mul_le_mul_of_nonneg_right hhalf34 (Nat.cast_nonneg N))
  have hN1 : (1 : ℝ) ≤ N := by
    have hp : 0 < 2 ^ k * Q := by positivity
    exact_mod_cast hp.trans_le hQN
  have hs : ((quadraticResidues Q).card : ℝ) ≤ Q := by
    exact_mod_cast (by simpa using card_le_univ (quadraticResidues Q) :
      (quadraticResidues Q).card ≤ Q)
  have ht := mul_le_mul (hs.trans hQr) (show (N : ℝ) + 1 ≤ 2 * N by linarith)
    (by positivity : (0 : ℝ) ≤ N + 1) (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k * N)
  have hd' := mul_le_mul_of_nonneg_right hd
    (show (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2 by positivity)
  have hb := max_square_sidon_real_modular_bound N Q
  have hsq : ((Real.sqrt (3 / 4) : ℝ) ^ k) ^ 2 = (3 / 4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
  nlinarith

lemma square_sidon_primorial_parametric_upper (n N : ℕ) (hn : 0 < n)
    (hN : 128 ^ n ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun m : ℕ => m ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ (sievePrimes n).card * N := by
  apply square_sidon_upper_of_modulus _ _ (sievePrimorial n) (sievePrimorial_pos n)
  · calc
      _ ≤ 2 ^ (3 * n) * 4 ^ (2 * n) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega)
          ((sievePrimes_card_le n).trans (by omega))) (sievePrimorial_le n)
      _ = 128 ^ n := by rw [pow_mul, pow_mul, ← mul_pow]; norm_num
      _ ≤ N := hN
  · exact sievePrimorial_density n

lemma square_sidon_primorial_upper (N : ℕ) (hN : 128 ^ 128 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * N * Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
  let n := Nat.log 128 N
  let k := (sievePrimes n).card
  have hn128 : 128 ≤ n := Nat.le_log_of_pow_le (by omega) hN
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn128R : (128 : ℝ) ≤ n := by exact_mod_cast hn128
  have hNp : 0 < N := (by positivity : 0 < (128 : ℕ) ^ 128).trans_le hN
  have hNpR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hpow : 128 ^ n ≤ N := Nat.pow_log_le_self 128 hNp.ne'
  have hpowR : (128 : ℝ) ^ n ≤ N := by exact_mod_cast hpow
  have hupper : (N : ℝ) ≤ (128 : ℝ) ^ (n + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < (128 : ℕ)) N).le
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hlog128lo : 1 ≤ Real.log 128 := by linarith
  have hlog128hi : Real.log 128 ≤ 7 := by linarith
  have hlo : (n : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 128 ^ n) hpowR
    rw [Real.log_pow] at h
    nlinarith
  have hhi : Real.log N ≤ 8 * n := by
    have h := Real.log_le_log hNpR hupper
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith
  have hloglog : 0 < Real.log (Real.log N) :=
    Real.log_pos (by linarith)
  have hlogn : Real.log n ≤ Real.log (Real.log N) := Real.log_le_log hnp hlo
  have hk : Real.log N ≤ 64 * k * Real.log (Real.log N) := by
    have hc := sievePrimes_card_log_lower n hn128
    change (n : ℝ) / 8 ≤ (k : ℝ) * Real.log n at hc
    have ht := mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have hquot : Real.log N / (512 * Real.log (Real.log N)) ≤ (k : ℝ) / 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hrlog : Real.log (Real.sqrt (3 / 4)) ≤ -(1 / 8 : ℝ) := by
    rw [Real.log_sqrt (by norm_num)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    linarith
  have hrpow : (Real.sqrt (3 / 4) : ℝ) ^ k ≤ Real.exp (-(k : ℝ) / 8) := by
    calc
      _ = Real.exp ((k : ℝ) * Real.log (Real.sqrt (3 / 4))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_left hrlog (Nat.cast_nonneg (α := ℝ) k)
        linarith)
  have he : Real.exp (-(k : ℝ) / 8) ≤
      Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hquot
  have hm := square_sidon_primorial_parametric_upper n N (by omega) hpow
  calc
    _ ≤ 2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := hm
    _ ≤ 2 * N * Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
      have h := mul_le_mul_of_nonneg_left (hrpow.trans he)
        (show (0 : ℝ) ≤ 2 * N by positivity)
      nlinarith



/--
What is the size of the largest Sidon subset $A\subseteq\{1,2^2,\ldots,N^2\}$? Is it $N^{1-o(1)}$?
-/
theorem erdos_773 :
    (∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤
        (Finset.maxSidonSubsetCard
          (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ)) := by
  intro ε hε
  by_cases hlarge : 1 / 3 < ε
  · exact conjecture_for_epsilon_gt_third ε hlarge
  · sorry

end Erdos773

#print axioms Erdos773.conjecture_for_epsilon_gt_third
#print axioms Erdos773.square_sidon_density_zero
#print axioms Erdos773.square_sidon_primorial_upper
