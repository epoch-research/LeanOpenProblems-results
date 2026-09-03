import Submission.LocalSmoothBudget
import Submission.SquarefreeInput

/-!
# Separating a smooth-prime core from an inverse-totient fiber

Finite support inequalities used to retain attained exponents in a restricted
squarefree fiber. These results do not increase the exponent.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

noncomputable def gSquarefreeOn (R : ℕ → Prop) (n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ totient m = n ∧ ∀ p ∈ m.primeFactors, R p}.ncard

lemma finite_squarefreeOn_fiber (R : ℕ → Prop) (n : ℕ) :
    {m : ℕ | Squarefree m ∧ totient m = n ∧ ∀ p ∈ m.primeFactors, R p}.Finite :=
  (finite_totient_fiber n).subset (fun _ hm => hm.2.1)

lemma gSquarefreeOn_le_g (R : ℕ → Prop) (n : ℕ) : gSquarefreeOn R n ≤ g n :=
  Set.ncard_le_ncard (fun _ hm => hm.2.1) (finite_totient_fiber n)

noncomputable def coreSupports (R : ℕ → Prop) (n : ℕ) : Finset (Finset ℕ) :=
  ((shiftedPrimeDivisors n).filter R).powerset.filter
    (fun S => (∏ p ∈ S, (p-1)) ∣ n)

lemma mem_coreSupports {R : ℕ → Prop} {n : ℕ} {S : Finset ℕ} :
    S ∈ coreSupports R n ↔
      S ⊆ (shiftedPrimeDivisors n).filter R ∧ (∏ p ∈ S, (p-1)) ∣ n := by
  simp [coreSupports]

/-- Weighted support counting after splitting the input primes by any predicate. -/
lemma support_sum_le_core_mul_rough (R : ℕ → Prop) (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) :
    (∑ S ∈ admissibleSupports n, ∏ p ∈ S, w p) ≤
      (∑ S ∈ coreSupports R n, ∏ p ∈ S, w p) *
        ∏ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬R p), (1+w p) := by
  let B := (shiftedPrimeDivisors n).filter (fun p => ¬R p)
  let f : Finset ℕ → Finset ℕ × Finset ℕ :=
    fun S => (S.filter R, S.filter (fun p => ¬R p))
  let v : Finset ℕ × Finset ℕ → ℝ := fun z => (∏ p ∈ z.1, w p)*(∏ p ∈ z.2, w p)
  have hf (S : Finset ℕ) (hS : S ∈ admissibleSupports n) :
      f S ∈ (coreSupports R n) ×ˢ B.powerset := by
    obtain ⟨hSP, hSd, _⟩ := Finset.mem_filter.mp hS
    have hsub := Finset.mem_powerset.mp hSP
    apply Finset.mem_product.mpr
    constructor
    · apply mem_coreSupports.mpr
      constructor
      · intro p hp
        obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hsub hpS, hpR⟩
      · exact (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p-1)
          (Finset.filter_subset R S)).trans hSd
    · apply Finset.mem_powerset.mpr
      intro p hp
      obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hsub hpS, hpR⟩
  have hinj : Set.InjOn f (↑(admissibleSupports n) : Set (Finset ℕ)) := by
    intro S hS T hT he
    have h := congrArg (fun z : Finset ℕ × Finset ℕ => z.1 ∪ z.2) he
    simpa only [f, Finset.filter_union_filter_not_eq] using h
  have he (S : Finset ℕ) : v (f S) = ∏ p ∈ S, w p :=
    Finset.prod_filter_mul_prod_filter_not S R w
  calc
    _ = ∑ S ∈ admissibleSupports n, v (f S) := Finset.sum_congr rfl (fun S _ => (he S).symm)
    _ = ∑ z ∈ (admissibleSupports n).image f, v z := (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ (coreSupports R n) ×ˢ B.powerset, v z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hz
        exact hf S hS
      · intro z hz hz'
        exact mul_nonneg (Finset.prod_nonneg (fun p _ => hw p))
          (Finset.prod_nonneg (fun p _ => hw p))
    _ = _ := by
      rw [Finset.sum_product]
      change (∑ S ∈ coreSupports R n, ∑ T ∈ B.powerset,
        (∏ p ∈ S, w p)*(∏ p ∈ T, w p)) = _
      rw [← Finset.sum_mul_sum, ← Finset.prod_one_add]

lemma coreSupport_fiber_card_le (R : ℕ → Prop) (n d : ℕ) :
    ((coreSupports R n).filter (fun S => (∏ p ∈ S, (p-1)) = d)).card ≤
      gSquarefreeOn R d := by
  let F := (coreSupports R n).filter (fun S => (∏ p ∈ S, (p-1)) = d)
  let I := F.image (fun S => ∏ p ∈ S, p)
  have hpr (S : Finset ℕ) (hS : S ∈ F) : ∀ p ∈ S, p.Prime := by
    intro p hp
    have h := (mem_coreSupports.mp (Finset.mem_filter.mp hS).1).1 hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑F : Set (Finset ℕ)) := by
    intro S hS T hT he
    have h := congrArg Nat.primeFactors he
    simpa only [Nat.primeFactors_prod (hpr S hS), Nat.primeFactors_prod (hpr T hT)] using h
  have hsub : (↑I : Set ℕ) ⊆
      {m : ℕ | Squarefree m ∧ totient m = d ∧ ∀ p ∈ m.primeFactors, R p} := by
    intro m hm
    change m ∈ F.image (fun S => ∏ p ∈ S, p) at hm
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    refine ⟨squarefree_prod_of_primes S (hpr S hS), ?_, ?_⟩
    · rw [totient_prod_primes S (hpr S hS)]
      exact (Finset.mem_filter.mp hS).2
    · rw [Nat.primeFactors_prod (hpr S hS)]
      intro p hp
      exact (Finset.mem_filter.mp ((mem_coreSupports.mp (Finset.mem_filter.mp hS).1).1 hp)).2
  have h := Set.ncard_le_ncard hsub (finite_squarefreeOn_fiber R d)
  simpa only [Set.ncard_coe_finset, I, Finset.card_image_of_injOn hinj, gSquarefreeOn] using h

lemma core_support_weight_sum_le (R : ℕ → Prop) (n : ℕ) (hn : 0 < n) (s : ℝ) :
    (∑ S ∈ coreSupports R n, ∏ p ∈ S, ((p-1 : ℕ) : ℝ)^(-s)) ≤
      ∑ d ∈ n.divisors, (gSquarefreeOn R d : ℝ)*(d : ℝ)^(-s) := by
  have hmap (S : Finset ℕ) (hS : S ∈ coreSupports R n) :
      (∏ p ∈ S, (p-1)) ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨(mem_coreSupports.mp hS).2, hn.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro d hd
  have he (S : Finset ℕ)
      (hS : S ∈ (coreSupports R n).filter (fun S => (∏ p ∈ S, (p-1)) = d)) :
      (∏ p ∈ S, ((p-1 : ℕ) : ℝ)^(-s)) = (d : ℝ)^(-s) := by
    rw [Real.finset_prod_rpow S _ (fun p _ => Nat.cast_nonneg (p-1)), ← Nat.cast_prod,
      (Finset.mem_filter.mp hS).2]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast coreSupport_fiber_card_le R n d)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)

lemma g_weight_le_core_sum_mul_rough (R : ℕ → Prop) (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) :
    (g n : ℝ)*(n : ℝ)^(-s) ≤
      (∑ d ∈ n.divisors, (gSquarefreeOn R d : ℝ)*(d : ℝ)^(-s)) *
        ∏ p ∈ (shiftedPrimeDivisors n).filter (fun p => ¬R p),
          (1+((p-1 : ℕ) : ℝ)^(-s)) := by
  let w : ℕ → ℝ := fun p => ((p-1 : ℕ) : ℝ)^(-s)
  have hpoint (S : Finset ℕ) (hS : S ∈ admissibleSupports n) :
      (n : ℝ)^(-s) ≤ ∏ p ∈ S, w p := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hpr (p : ℕ) (hp : p ∈ S) : p.Prime := (Finset.mem_filter.mp (hsub hp)).2.1
    have hpos : 0 < ∏ p ∈ S, (p-1) :=
      Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hpr p hp).one_lt)
    have hle := Nat.le_of_dvd hn (Finset.mem_filter.mp hS).2.1
    have h := Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < ((∏ p ∈ S, (p-1) : ℕ) : ℝ) by exact_mod_cast hpos)
      (show ((∏ p ∈ S, (p-1) : ℕ) : ℝ) ≤ n by exact_mod_cast hle)
      (neg_nonpos.mpr hs)
    simpa only [Nat.cast_prod, ← Real.finset_prod_rpow S
      (fun p => ((p-1 : ℕ) : ℝ)) (fun p _ => Nat.cast_nonneg _) (-s), w] using h
  calc
    _ = ∑ _S ∈ admissibleSupports n, (n : ℝ)^(-s) := by
      rw [Finset.sum_const, nsmul_eq_mul, g_eq_card_admissibleSupports hn]
    _ ≤ ∑ S ∈ admissibleSupports n, ∏ p ∈ S, w p := Finset.sum_le_sum hpoint
    _ ≤ _ := (support_sum_le_core_mul_rough R n w (fun p => by dsimp [w]; positivity)).trans
      (mul_le_mul_of_nonneg_right (core_support_weight_sum_le R n hn s)
        (Finset.prod_nonneg (fun p _ => by positivity)))

lemma rough_shifted_weight_sum_le (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    (∑ p ∈ (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k),
      ((p-1 : ℕ) : ℝ)^(-s)) ≤
      (1/(1-s))*∑ q ∈ n.primeFactors, (q : ℝ)^((k : ℝ)*(1-s)-1) := by
  let P := (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k)
  let D := P.image (fun p => p-1)
  have hD (d : ℕ) (hd : d ∈ D) :
      0 < d ∧ (d+1).Prime ∧ d ∣ n ∧ d ∉ smoothShiftedPredecessors k := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hpP, hpR⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpp, hpd⟩ := Finset.mem_filter.mp hpP
    exact ⟨Nat.sub_pos_of_lt hpp.one_lt,
      by simpa only [Nat.sub_add_cancel hpp.one_lt.le] using hpp, hpd, hpR⟩
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq h
    change p ∈ (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k) at hp
    change q ∈ (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k) at hq
    have hp2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.two_le
    have hq2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.two_le
    change p-1 = q-1 at h
    omega
  change (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s)) ≤ _
  rw [← Finset.sum_image (f := fun d : ℕ => (d : ℝ)^(-s)) hinj]
  apply rough_divisor_weight_sum_sharp D n.primeFactors k hk s hs hs1
    (fun d hd => (hD d hd).1) (fun q hq => Nat.pos_of_mem_primeFactors hq)
  intro d hd
  have hnot : ¬∀ q ∈ d.primeFactors, q^k ≤ d :=
    fun h => (hD d hd).2.2.2 ⟨(hD d hd).2.1, h⟩
  push_neg at hnot
  obtain ⟨q, hq, hqd⟩ := hnot
  exact ⟨q, Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
    (Nat.dvd_of_mem_primeFactors hq).trans (hD d hd).2.2.1, hn.ne'⟩,
    Nat.dvd_of_mem_primeFactors hq, hqd.le⟩

lemma rough_shifted_weight_sum_endpoint (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k),
      ((p-1 : ℕ) : ℝ)^(-(1-1/(k : ℝ)))) ≤ (k : ℝ)*n.primeFactors.card := by
  have hb := reciprocal_exponent_bounds k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℝ)*(1-(1-1/(k : ℝ)))-1 = 0 := by field_simp; ring
  have h := rough_shifted_weight_sum_le k hk n hn (1-1/(k : ℝ)) hb.1 hb.2
  rw [he] at h
  simpa only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    sub_sub_cancel, one_div_one_div] using h

noncomputable def gSmoothCore (k n : ℕ) : ℕ :=
  gSquarefreeOn (fun p => p-1 ∈ smoothShiftedPredecessors k) n

/-- A finite convolution-style upper bound: the full fiber is controlled by
smooth-core fibers at divisor outputs, with an explicit subpower rough cost. -/
theorem g_le_smooth_core_divisor_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ)^(1-1/(k : ℝ)) * Real.exp ((k : ℝ)*n.primeFactors.card) *
      ∑ d ∈ n.divisors, (gSmoothCore k d : ℝ)*(d : ℝ)^(-(1-1/(k : ℝ))) := by
  let s := 1-1/(k : ℝ)
  let Q := (shiftedPrimeDivisors n).filter (fun p => p-1 ∉ smoothShiftedPredecessors k)
  let M := ∑ d ∈ n.divisors, (gSmoothCore k d : ℝ)*(d : ℝ)^(-s)
  have hb := reciprocal_exponent_bounds k hk
  have hM : 0 ≤ M := Finset.sum_nonneg (fun d _ => by positivity)
  have hprod : (∏ p ∈ Q, (1+((p-1 : ℕ) : ℝ)^(-s))) ≤
      Real.exp ((k : ℝ)*n.primeFactors.card) := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (((p-1 : ℕ) : ℝ)^(-s)) := by
        apply Finset.prod_le_prod
        · intro p hp
          positivity
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (((p-1 : ℕ) : ℝ)^(-s))
      _ = Real.exp (∑ p ∈ Q, ((p-1 : ℕ) : ℝ)^(-s)) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (rough_shifted_weight_sum_endpoint k hk n hn)
  have h := g_weight_le_core_sum_mul_rough
    (fun p => p-1 ∈ smoothShiftedPredecessors k) n hn s hb.1
  change (g n : ℝ)*(n : ℝ)^(-s) ≤ M*(∏ p ∈ Q, (1+((p-1 : ℕ) : ℝ)^(-s))) at h
  have hbound := h.trans (mul_le_mul_of_nonneg_left hprod hM)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (g n : ℝ) = ((g n : ℝ)*(n : ℝ)^(-s))*(n : ℝ)^s := by
      rw [mul_assoc, ← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ (M*Real.exp ((k : ℝ)*n.primeFactors.card))*(n : ℝ)^s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hnR.le s)
    _ = _ := by change (M*Real.exp _)*(n : ℝ)^s = (n : ℝ)^s*Real.exp _*M; ring

lemma eventually_core_rough_cost_le_rpow (k : ℕ) (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*n.divisors.card*Real.exp ((k : ℝ)*n.primeFactors.card) ≤
      (n : ℝ)^ε := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA⟩ := exists_sum_primeFactors_rpow_nonpos_le_log 0 k δ
    (by norm_num) (Nat.cast_nonneg _) hδ
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_card_divisors_le_rpow δ hδ, eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (C*Real.exp A))] with n hnτ hn hnC
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hω := hA n hn0
  simp only [neg_zero, Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at hω
  have hExp : Real.exp ((k : ℝ)*n.primeFactors.card) ≤ Real.exp A*(n : ℝ)^δ := by
    calc
      _ ≤ Real.exp (A+δ*Real.log n) := Real.exp_le_exp.mpr hω
      _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hnR]; congr 1; congr 1; ring
  calc
    _ ≤ C*(n : ℝ)^δ*(Real.exp A*(n : ℝ)^δ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnτ hC) hExp
        (Real.exp_pos _).le (mul_nonneg hC (Real.rpow_nonneg hnR.le δ))
    _ = (C*Real.exp A)*((n : ℝ)^δ*(n : ℝ)^δ) := by ring
    _ ≤ (n : ℝ)^δ*((n : ℝ)^δ*(n : ℝ)^δ) :=
      mul_le_mul_of_nonneg_right hnC (by positivity)
    _ = (n : ℝ)^ε := by
      rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
      congr 1
      dsimp [δ]
      ring

lemma g_le_of_global_smooth_core_bound (k : ℕ) (hk : 1 ≤ k) (C t : ℝ)
    (hC : 0 ≤ C) (ht : 1-1/(k : ℝ) ≤ t)
    (H : ∀ d : ℕ, 0 < d → (gSmoothCore k d : ℝ) ≤ C*(d : ℝ)^t)
    (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (C*n.divisors.card*Real.exp ((k : ℝ)*n.primeFactors.card))*(n : ℝ)^t := by
  let s := 1-1/(k : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ d ∈ n.divisors, (gSmoothCore k d : ℝ)*(d : ℝ)^(-s)) ≤
      C*n.divisors.card*(n : ℝ)^(t-s) := by
    calc
      _ ≤ ∑ d ∈ n.divisors, C*(n : ℝ)^(t-s) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 := Nat.pos_of_mem_divisors hd
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
        calc
          _ ≤ (C*(d : ℝ)^t)*(d : ℝ)^(-s) :=
            mul_le_mul_of_nonneg_right (H d hd0) (Real.rpow_nonneg hdR.le _)
          _ = C*(d : ℝ)^(t-s) := by rw [mul_assoc, ← Real.rpow_add hdR]; rfl
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hdR.le (by exact_mod_cast Nat.divisor_le hd)
              (sub_nonneg.mpr ht)) hC
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have h := (g_le_smooth_core_divisor_sum k hk n hn).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  apply h.trans_eq
  change (n : ℝ)^s*Real.exp _*(C*n.divisors.card*(n : ℝ)^(t-s)) = _
  calc
    _ = (C*n.divisors.card*Real.exp ((k : ℝ)*n.primeFactors.card))*
        ((n : ℝ)^s*(n : ℝ)^(t-s)) := by ring
    _ = _ := by rw [← Real.rpow_add hnR, add_sub_cancel]

/-- Above the rough endpoint, an eventual upper bound on smooth-core
multiplicity transfers to the full fiber with arbitrarily small exponent loss. -/
theorem eventually_g_le_of_smooth_core_bound (k : ℕ) (hk : 1 ≤ k)
    (t u : ℝ) (ht : 1-1/(k : ℝ) ≤ t) (htu : t < u)
    (H : ∀ᶠ n : ℕ in atTop, (gSmoothCore k n : ℝ) ≤ (n : ℝ)^t) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp H
  let C : ℝ := 1 + ∑ d ∈ Finset.range N, (gSmoothCore k d : ℝ)
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
  have ht0 : 0 ≤ t := (reciprocal_exponent_bounds k hk).1.trans ht
  have hglobal (d : ℕ) (hd : 0 < d) : (gSmoothCore k d : ℝ) ≤ C*(d : ℝ)^t := by
    by_cases hNd : N ≤ d
    · exact (hN d hNd).trans (le_mul_of_one_le_left (by positivity) hC)
    · have hsmall : (gSmoothCore k d : ℝ) ≤ C := by
        have h := Finset.single_le_sum
          (fun i (_ : i ∈ Finset.range N) => Nat.cast_nonneg (α := ℝ) (gSmoothCore k i))
          (Finset.mem_range.mpr (Nat.lt_of_not_ge hNd))
        dsimp [C]
        linarith
      exact hsmall.trans (le_mul_of_one_le_right (by linarith : 0 ≤ C)
        (Real.one_le_rpow (by exact_mod_cast hd) ht0))
  filter_upwards [eventually_core_rough_cost_le_rpow k C (u-t) (by linarith)
    (sub_pos.mpr htu), eventually_ge_atTop 1] with n hnC hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    (g n : ℝ) ≤ (C*n.divisors.card*Real.exp ((k : ℝ)*n.primeFactors.card))*(n : ℝ)^t :=
      g_le_of_global_smooth_core_bound k hk C t (by linarith) ht hglobal n hn0
    _ ≤ (n : ℝ)^(u-t)*(n : ℝ)^t :=
      mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ)^u := by rw [← Real.rpow_add hnR, sub_add_cancel]

/-- An already attained exponent above 1-1/k survives restriction to
squarefree inputs all of whose prime predecessors are root-k smooth,
with any strictly positive loss. This is not an exponent increase. -/
theorem infinite_gSmoothCore_gt_of_infinite_g_gt (k : ℕ) (hk : 1 ≤ k)
    (β γ : ℝ) (hβ : 1-1/(k : ℝ) ≤ β) (hβγ : β < γ)
    (H : {n : ℕ | (n : ℝ)^γ < g n}.Infinite) :
    {n : ℕ | (n : ℝ)^β < gSmoothCore k n}.Infinite := by
  by_contra h
  have hf : {n : ℕ | (n : ℝ)^β < gSmoothCore k n}.Finite := Set.not_infinite.mp h
  obtain ⟨B, hB⟩ := hf.bddAbove
  have hev : ∀ᶠ n : ℕ in atTop, (gSmoothCore k n : ℝ) ≤ (n : ℝ)^β := by
    filter_upwards [eventually_ge_atTop (B+1)] with n hn
    apply le_of_not_gt
    intro hng
    have := hB hng
    omega
  have hg := eventually_g_le_of_smooth_core_bound k hk β γ hβ hβγ hev
  obtain ⟨N, hN⟩ := eventually_atTop.mp hg
  obtain ⟨n, hn, hnN⟩ := H.exists_gt N
  exact (hN n hnN.le).not_gt hn

end Erdos821
