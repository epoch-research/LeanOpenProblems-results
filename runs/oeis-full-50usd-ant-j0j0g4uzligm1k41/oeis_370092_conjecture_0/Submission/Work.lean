import FormalConjectures.Util.ProblemImports

open Finset Nat

noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1
      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j
      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

/-- Each coefficient `1 - (-1)^(j+1) - (-2)^(j+1)` is an even integer. -/
lemma coeff_even (j : ℕ) : Even (1 - (-1 : ℤ)^(j+1) - (-2 : ℤ)^(j+1)) := by
  have h1 : Even (1 - (-1 : ℤ)^(j+1)) := by
    rcases Nat.even_or_odd (j+1) with he | ho
    · rw [he.neg_one_pow]; decide
    · rw [ho.neg_one_pow]; decide
  have h2 : Even ((-2 : ℤ)^(j+1)) := by
    rw [pow_succ]
    exact (even_neg.mpr (even_two)).mul_left _
  exact (h1.sub h2)

/-- The rational coefficient equals two times an integer. -/
lemma coeff_eq_two_mul (j : ℕ) :
    ∃ c : ℤ, (1 - (-1 : ℚ)^(j+1) - (-2 : ℚ)^(j+1)) = 2 * (c : ℚ) := by
  obtain ⟨c, hc⟩ := coeff_even j
  refine ⟨c, ?_⟩
  have hcast : ((1 - (-1 : ℤ)^(j+1) - (-2 : ℤ)^(j+1) : ℤ) : ℚ) = ((c + c : ℤ) : ℚ) := by
    rw [hc]
  push_cast at hcast ⊢
  linarith [hcast]

/-- `a n` is always an integer. -/
theorem a_isInt : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨1, by simp [a]⟩
    | m + 1 =>
      -- unfold definition
      have hdef : a (m+1) = (-1 : ℚ)^(m+1) + (1 / 2) *
          (Finset.sum (Finset.range (m+1)) (fun k =>
            (((m+1).choose (k+1) : ℚ)) * (1 - (-1 : ℚ)^(k+1) - (-2 : ℚ)^(k+1))
              * a ((m+1) - (k+1)))) := by
        conv_lhs => rw [a]
      -- integrality of the shifted terms (holds for all k by truncated subtraction)
      have hz : ∀ k : ℕ, ∃ z : ℤ, a ((m+1) - (k+1)) = (z : ℚ) := by
        intro k; exact ih ((m+1) - (k+1)) (by omega)
      choose z hz using hz
      have hc : ∀ k : ℕ, ∃ c : ℤ, (1 - (-1 : ℚ)^(k+1) - (-2 : ℚ)^(k+1)) = 2 * (c : ℚ) :=
        coeff_eq_two_mul
      choose c hc using hc
      -- each summand equals 2 * (integer)
      have hterm : ∀ k : ℕ,
          (((m+1).choose (k+1) : ℚ)) * (1 - (-1 : ℚ)^(k+1) - (-2 : ℚ)^(k+1))
              * a ((m+1) - (k+1))
          = 2 * ((((m+1).choose (k+1) : ℤ) * c k * z k : ℤ) : ℚ) := by
        intro k
        rw [hc k, hz k]
        push_cast
        ring
      -- sum equals 2 * (integer sum)
      have hsum : (Finset.sum (Finset.range (m+1)) (fun k =>
            (((m+1).choose (k+1) : ℚ)) * (1 - (-1 : ℚ)^(k+1) - (-2 : ℚ)^(k+1))
              * a ((m+1) - (k+1))))
          = 2 * ((Finset.sum (Finset.range (m+1))
              (fun k => ((m+1).choose (k+1) : ℤ) * c k * z k) : ℤ) : ℚ) := by
        rw [Finset.sum_congr rfl (fun k _ => hterm k)]
        rw [← Finset.mul_sum]
        push_cast
        ring
      -- conclude
      refine ⟨(-1 : ℤ)^(m+1) +
        (Finset.sum (Finset.range (m+1)) (fun k => ((m+1).choose (k+1) : ℤ) * c k * z k)), ?_⟩
      rw [hdef, hsum]
      push_cast
      ring


/-- The integer sequence underlying `a`. -/
noncomputable def A (n : ℕ) : ℤ := (a n).num

/-- `a n` is the rational cast of the integer `A n`. -/
lemma a_eq_A (n : ℕ) : a n = (A n : ℚ) := by
  obtain ⟨z, hz⟩ := a_isInt n
  rw [A, hz]
  simp

/-- Reduction mod `k` of `a` (as in the conjecture) equals the reduction of the integer `A n`. -/
lemma aMod_eq (k : ℕ) (n : ℕ) : ((a n).num : ZMod k) = (A n : ZMod k) := rfl

/-- Any orbit of a self-map on a finite type is eventually periodic. -/
theorem eventually_periodic_orbit {X : Type*} [Finite X] (f : X → X) (x : X) :
    ∃ N P : ℕ, 0 < P ∧ ∀ n : ℕ, N ≤ n → f^[n + P] x = f^[n] x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x)
  -- order i, j so that a < b
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨i, j - i, by omega, ?_⟩
    intro n hn
    have hj : i + (j - i) = j := by omega
    calc f^[n + (j - i)] x
        = f^[n - i] (f^[i + (j - i)] x) := by
          rw [← Function.iterate_add_apply]; congr 1; omega
      _ = f^[n - i] (f^[i] x) := by rw [hj]; exact congrArg _ heq.symm
      _ = f^[n] x := by rw [← Function.iterate_add_apply]; congr 1; omega
  · refine ⟨j, i - j, by omega, ?_⟩
    intro n hn
    have hi : j + (i - j) = i := by omega
    calc f^[n + (i - j)] x
        = f^[n - j] (f^[j + (i - j)] x) := by
          rw [← Function.iterate_add_apply]; congr 1; omega
      _ = f^[n - j] (f^[j] x) := by rw [hi]; exact congrArg _ heq
      _ = f^[n] x := by rw [← Function.iterate_add_apply]; congr 1; omega

/-- The Stirling recurrence realises `n ↦ (S(n,0),…,S(n,r))` as an orbit of a fixed
self-map on the finite state space `Fin (r+1) → ZMod m`; hence each `S(·,r) mod m`
is eventually periodic. -/
theorem stirlingSecond_eventually_periodic (m r : ℕ) [NeZero m] :
    ∃ N P : ℕ, 0 < P ∧ ∀ n : ℕ, N ≤ n →
      (Nat.stirlingSecond (n + P) r : ZMod m) = (Nat.stirlingSecond n r : ZMod m) := by
  classical
  set X := (Fin (r+1) → ZMod m) with hX
  set T : X → X := fun v j =>
      (j.val : ZMod m) * v j + (if h : j.val = 0 then 0 else v ⟨j.val - 1, by omega⟩) with hT
  set s0 : X := fun j => (Nat.stirlingSecond 0 j.val : ZMod m) with hs0
  have hstate : ∀ n : ℕ, ∀ j : Fin (r+1),
      (T^[n] s0) j = (Nat.stirlingSecond n j.val : ZMod m) := by
    intro n
    induction n with
    | zero => intro j; simp [hs0]
    | succ n ih =>
      intro j
      rw [Function.iterate_succ_apply', hT]
      simp only
      rw [ih j]
      by_cases hj : j.val = 0
      · rw [dif_pos hj]
        have : Nat.stirlingSecond (n+1) j.val = 0 := by
          rw [hj]; exact Nat.stirlingSecond_succ_zero n
        rw [this, hj]
        push_cast
        ring
      · rw [dif_neg hj, ih ⟨j.val - 1, by omega⟩]
        -- write j.val = k+1
        obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
        have hrec : Nat.stirlingSecond (n+1) j.val
            = j.val * Nat.stirlingSecond n j.val + Nat.stirlingSecond n (j.val - 1) := by
          rw [hk]
          simpa using Nat.stirlingSecond_succ_succ n k
        rw [hrec]
        push_cast
        ring
  obtain ⟨N, P, hP, hper⟩ := eventually_periodic_orbit T s0
  refine ⟨N, P, hP, ?_⟩
  intro n hn
  have hcomp := congrFun (hper n hn) (⟨r, by omega⟩ : Fin (r+1))
  rw [hstate (n + P) ⟨r, by omega⟩, hstate n ⟨r, by omega⟩] at hcomp
  simpa using hcomp

/-- Eventual periodicity predicate for a sequence into `ZMod k`. -/
def EvPeriodic {k : ℕ} (f : ℕ → ZMod k) : Prop :=
  ∃ N P : ℕ, 0 < P ∧ ∀ n : ℕ, N ≤ n → f (n + P) = f n

namespace EvPeriodic

variable {k : ℕ}

/-- With a period `P`, any multiple `m * P` is also a period (past the threshold). -/
lemma iterate {f : ℕ → ZMod k} {N P : ℕ} (h : ∀ n : ℕ, N ≤ n → f (n + P) = f n)
    (m : ℕ) : ∀ n : ℕ, N ≤ n → f (n + m * P) = f n := by
  induction m with
  | zero => intro n hn; simp
  | succ m ih =>
    intro n hn
    have hrw : n + (m + 1) * P = (n + m * P) + P := by ring
    rw [hrw, h (n + m * P) (by omega), ih n hn]

lemma const (c : ZMod k) : EvPeriodic (fun _ => c) := ⟨0, 1, one_pos, fun _ _ => rfl⟩

lemma add {f g : ℕ → ZMod k} (hf : EvPeriodic f) (hg : EvPeriodic g) :
    EvPeriodic (fun n => f n + g n) := by
  obtain ⟨Nf, Pf, hPf, hf⟩ := hf
  obtain ⟨Ng, Pg, hPg, hg⟩ := hg
  refine ⟨max Nf Ng, Pf * Pg, Nat.mul_pos hPf hPg, ?_⟩
  intro n hn
  have e1 : f (n + Pf * Pg) = f n := by
    have h := iterate hf Pg n (le_trans (le_max_left _ _) hn)
    rwa [Nat.mul_comm Pg Pf] at h
  have e2 : g (n + Pf * Pg) = g n := iterate hg Pf n (le_trans (le_max_right _ _) hn)
  show f (n + Pf * Pg) + g (n + Pf * Pg) = f n + g n
  rw [e1, e2]

lemma smul {f : ℕ → ZMod k} (c : ZMod k) (hf : EvPeriodic f) :
    EvPeriodic (fun n => c * f n) := by
  obtain ⟨N, P, hP, hf⟩ := hf
  refine ⟨N, P, hP, fun n hn => ?_⟩
  show c * f (n + P) = c * f n
  rw [hf n hn]

lemma sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ZMod k)
    (h : ∀ i ∈ s, EvPeriodic (F i)) :
    EvPeriodic (fun n => ∑ i ∈ s, F i n) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using const 0
  | insert i s hi ih =>
    have hI : EvPeriodic (F i) := h i (Finset.mem_insert_self _ _)
    have hs : EvPeriodic (fun n => ∑ j ∈ s, F j n) :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hadd := hI.add hs
    have hfun : (fun n => ∑ j ∈ insert i s, F j n) = (fun n => F i n + ∑ j ∈ s, F j n) := by
      funext n; rw [Finset.sum_insert hi]
    rw [hfun]
    exact hadd

end EvPeriodic

/-- `n ↦ S(n,r) mod k` is eventually periodic (repackaged as `EvPeriodic`). -/
lemma evPeriodic_stirling (k r : ℕ) [NeZero k] :
    EvPeriodic (fun n => (Nat.stirlingSecond n r : ZMod k)) :=
  stirlingSecond_eventually_periodic k r

/-- **Conditional eventual periodicity of `A mod k`.**
If `a(n)` reduces mod `k` to a finite Stirling combination `Σ_{r<R} H_r · S(n,r)`
(the truncated generating-function bridge), then `A mod k` is eventually periodic.
This isolates the *only* remaining gap for eventual periodicity: the bridge itself. -/
theorem A_evPeriodic_of_bridge (k R : ℕ) [NeZero k] (H : ℕ → ℤ)
    (hbridge : ∀ n : ℕ,
      (A n : ZMod k)
        = ∑ r ∈ Finset.range R, (H r : ZMod k) * (Nat.stirlingSecond n r : ZMod k)) :
    EvPeriodic (fun n => (A n : ZMod k)) := by
  have hfun : (fun n => (A n : ZMod k))
      = (fun n => ∑ r ∈ Finset.range R,
          (H r : ZMod k) * (Nat.stirlingSecond n r : ZMod k)) := by
    funext n; exact hbridge n
  rw [hfun]
  refine EvPeriodic.sum _ _ (fun r _ => ?_)
  exact EvPeriodic.smul (H r : ZMod k) (evPeriodic_stirling k r)

/-- Fixed-period eventual periodicity (this is exactly the conjecture's `eventually_periodic`). -/
def PeriodicWith {k : ℕ} (f : ℕ → ZMod k) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

namespace PeriodicWith
variable {k P : ℕ}

lemma const (c : ZMod k) : PeriodicWith (fun _ => c) P := ⟨0, fun _ _ => rfl⟩

lemma add {f g : ℕ → ZMod k} (hf : PeriodicWith f P) (hg : PeriodicWith g P) :
    PeriodicWith (fun n => f n + g n) P := by
  obtain ⟨Nf, hf⟩ := hf; obtain ⟨Ng, hg⟩ := hg
  refine ⟨max Nf Ng, fun n hn => ?_⟩
  show f (n + P) + g (n + P) = f n + g n
  rw [hf n (le_trans (le_max_left _ _) hn), hg n (le_trans (le_max_right _ _) hn)]

lemma smul {f : ℕ → ZMod k} (c : ZMod k) (hf : PeriodicWith f P) :
    PeriodicWith (fun n => c * f n) P := by
  obtain ⟨N, hf⟩ := hf
  refine ⟨N, fun n hn => ?_⟩
  show c * f (n + P) = c * f n
  rw [hf n hn]

lemma sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ZMod k)
    (h : ∀ i ∈ s, PeriodicWith (F i) P) :
    PeriodicWith (fun n => ∑ i ∈ s, F i n) P := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact const 0
  | insert i s hi ih =>
    have hadd := (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    have hfun : (fun n => ∑ j ∈ insert i s, F j n)
        = (fun n => F i n + ∑ j ∈ s, F j n) := by
      funext n; rw [Finset.sum_insert hi]
    rw [hfun]; exact hadd

end PeriodicWith

/-- **Powers of a unit are periodic with period `φ k`** (Fermat–Euler).
This is the arithmetic heart of the "period divides `φ(k)`" direction. -/
lemma unit_pow_periodicWith (k : ℕ) [NeZero k] (x : (ZMod k)ˣ) :
    PeriodicWith (fun n => ((x : ZMod k)) ^ n) (Nat.totient k) := by
  refine ⟨0, fun n _ => ?_⟩
  show ((x : ZMod k)) ^ (n + Nat.totient k) = ((x : ZMod k)) ^ n
  rw [pow_add]
  have h1 : ((x : ZMod k)) ^ (Nat.totient k) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient x, Units.val_one]
  rw [h1, mul_one]
