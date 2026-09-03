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
