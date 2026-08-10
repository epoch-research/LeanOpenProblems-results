import FormalConjectures.Util.ProblemImports

open Function

/-- Configuration as a function ℕ → ℕ. The CA step. -/
def stepf (f : ℕ → ℕ) : ℕ → ℕ :=
  fun i => (f i + 1) / 2 + (if i = 0 then 0 else f (i - 1) / 2)

/-- Add one token at position p. -/
def addE (f : ℕ → ℕ) (p : ℕ) : ℕ → ℕ :=
  fun i => f i + (if i = p then 1 else 0)

/-- The token advances when the local mass is odd. -/
def pnext (f : ℕ → ℕ) (p : ℕ) : ℕ := p + f p % 2

/-- Single-step coupling identity (universal). -/
theorem step_coupling (f : ℕ → ℕ) (p : ℕ) :
    stepf (addE f p) = addE (stepf f) (pnext f p) := by
  funext i
  simp only [stepf, addE, pnext]
  have hpar : f p % 2 = 0 ∨ f p % 2 = 1 := by omega
  cases i with
  | zero =>
    rcases hpar with h | h <;> simp only [h] <;>
      by_cases hp : (0 : ℕ) = p <;> simp_all <;> omega
  | succ j =>
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    rcases hpar with h | h <;> simp only [h] <;>
      by_cases h1 : j + 1 = p <;> by_cases h2 : j = p <;> simp_all <;> omega

/-! ## Support and gaplessness -/

/-- `f` is supported on `[0, N)`. -/
def Supp (f : ℕ → ℕ) (N : ℕ) : Prop := ∀ i, N ≤ i → f i = 0

/-- `f` is gapless: once zero, stays zero to the right. -/
def Gapless (f : ℕ → ℕ) : Prop := ∀ i, f i = 0 → f (i + 1) = 0

lemma stepf_zero_of (f : ℕ → ℕ) {i : ℕ} (hi : 0 < i) (h1 : f i = 0) (h2 : f (i-1) = 0) :
    stepf f i = 0 := by
  simp only [stepf]
  rw [if_neg (by omega)]
  rw [h1, h2]

lemma supp_stepf {f : ℕ → ℕ} {N : ℕ} (h : Supp f N) : Supp (stepf f) (N+1) := by
  intro i hi
  apply stepf_zero_of f (by omega)
  · exact h i (by omega)
  · exact h (i-1) (by omega)

lemma gapless_stepf {f : ℕ → ℕ} (h : Gapless f) : Gapless (stepf f) := by
  intro i hi
  -- stepf f i = 0 implies f i = 0
  have hfi : f i = 0 := by
    by_contra hne
    simp only [stepf] at hi
    split at hi <;> omega
  have hfi1 : f (i+1) = 0 := h i hfi
  -- stepf f (i+1) = (f(i+1)+1)/2 + f(i)/2 = 0
  have := stepf_zero_of f (i := i+1) (by omega) hfi1 (by simpa using hfi)
  exact this

/-! ## Mass conservation -/

open Finset in
/-- Mass over `[0, M)`. -/
def mass (M : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range M, f i

open Finset in
lemma mass_stepf {f : ℕ → ℕ} {M : ℕ} (h : Supp f M) :
    mass (M+1) (stepf f) = mass M f := by
  unfold mass
  -- ∑_{i<M+1} stepf f i
  have key : ∀ i, stepf f i = (f i + 1)/2 + (if i = 0 then 0 else f (i-1)/2) := fun i => rfl
  simp only [key]
  rw [Finset.sum_add_distrib]
  -- first sum: ∑_{i<M+1} (f i + 1)/2.  Peel last term (i=M), f M = 0.
  rw [Finset.sum_range_succ]
  rw [show f M = 0 from h M (le_refl M)]
  -- second sum via sum_range_succ'
  rw [Finset.sum_range_succ']
  simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, if_pos rfl, add_zero]
  -- now: (∑_{i<M}(f i+1)/2 + (0+1)/2) + ∑_{i<M} f i /2 = ∑_{i<M} f i
  norm_num
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  omega

/-! ## First moment monovariant -/

open Finset in
/-- First moment over `[0, M)`. -/
def mom (M : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range M, i * f i

open Finset in
/-- The "work" done in one step: total mass moving right. -/
def work (M : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range M, f i / 2

open Finset in
lemma mom_stepf {f : ℕ → ℕ} {M : ℕ} (h : Supp f M) :
    mom (M+1) (stepf f) = mom M f + work M f := by
  unfold mom work
  have key : ∀ i, i * stepf f i
      = i * ((f i + 1)/2) + (if i = 0 then 0 else i * (f (i-1)/2)) := by
    intro i
    simp only [stepf, Nat.mul_add]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    · rw [if_neg (by omega), if_neg (by omega)]
  simp only [key]
  rw [Finset.sum_add_distrib]
  -- ∑A over range(M+1) and ∑B over range(M+1)
  rw [Finset.sum_range_succ (fun i => i * ((f i + 1)/2)) M]
  rw [show f M = 0 from h M (le_refl M)]
  rw [Finset.sum_range_succ' (fun i => if i = 0 then 0 else i * (f (i-1)/2)) M]
  simp only [if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, if_pos rfl]
  -- goal: (∑_{i<M} i*((f i+1)/2) + M*((0+1)/2)) + (∑_{i<M} (i+1)*(f i/2) + 0)
  --        = ∑_{i<M} i*f i + ∑_{i<M} f i/2
  norm_num
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  -- i * ((f i + 1)/2) + (i+1) * (f i / 2) = i * f i + f i / 2
  rcases Nat.even_or_odd (f i) with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    rw [show (k + k + 1)/2 = k by omega, show (k + k)/2 = k by omega]; ring
  · rw [hk]
    rw [show (2*k + 1 + 1)/2 = k + 1 by omega, show (2*k + 1)/2 = k by omega]; ring

/-! ## Trajectory, support bound -/

/-- Initial config: mass `n` at position `0`. -/
def initf (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

/-- Target config: `1` on `[0, n)`. -/
def targetf (n : ℕ) : ℕ → ℕ := fun i => if i < n then 1 else 0

/-- The trajectory. -/
def traj (n t : ℕ) : ℕ → ℕ := (stepf)^[t] (initf n)

@[simp] lemma traj_zero (n : ℕ) : traj n 0 = initf n := rfl

lemma traj_succ (n t : ℕ) : traj n (t+1) = stepf (traj n t) := by
  unfold traj; rw [Function.iterate_succ']; rfl

lemma initf_gapless (n : ℕ) : Gapless (initf n) := by
  intro i hi; simp only [initf] at *; split at hi <;> simp_all

lemma initf_supp (n : ℕ) : Supp (initf n) 1 := by
  intro i hi; simp only [initf]; rw [if_neg (by omega)]

lemma traj_gapless (n t : ℕ) : Gapless (traj n t) := by
  induction t with
  | zero => exact initf_gapless n
  | succ t ih => rw [traj_succ]; exact gapless_stepf ih

lemma traj_supp_succ (n t : ℕ) : Supp (traj n t) (t+1) := by
  induction t with
  | zero => exact initf_supp n
  | succ t ih => rw [traj_succ]; exact supp_stepf ih

lemma traj_mass (n t : ℕ) : mass (t+1) (traj n t) = n := by
  induction t with
  | zero => simp [mass, initf]
  | succ t ih =>
    rw [traj_succ, mass_stepf (traj_supp_succ n t), ih]

/-- Downward closure for gapless configs. -/
lemma gapless_down {f : ℕ → ℕ} (hg : Gapless f) :
    ∀ i j, j ≤ i → f i ≠ 0 → f j ≠ 0 := by
  intro i
  induction i with
  | zero =>
    intro j hj h0
    interval_cases j
    exact h0
  | succ i ih =>
    intro j hj h0
    by_cases hji : j = i + 1
    · rwa [hji]
    · have hji' : j ≤ i := by omega
      have hfi : f i ≠ 0 := by
        intro hc; exact h0 (hg i hc)
      exact ih j hji' hfi

open Finset in
lemma supp_of_gapless_mass {f : ℕ → ℕ} {M n : ℕ}
    (hg : Gapless f) (hs : Supp f M) (hm : mass M f = n) : Supp f n := by
  intro i hi
  by_contra hne
  -- f i ≠ 0, i ≥ n
  have hiM : i < M := by
    by_contra hc; exact hne (hs i (by omega))
  -- all j ≤ i have f j ≥ 1
  have hall : ∀ j ∈ Finset.range (i+1), 1 ≤ f j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : f j ≠ 0 := gapless_down hg i j (by omega) hne
    omega
  have hsub : Finset.range (i+1) ⊆ Finset.range M := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have h1 : (i+1) ≤ mass M f := by
    calc i + 1 = ∑ _j ∈ Finset.range (i+1), 1 := by simp
      _ ≤ ∑ j ∈ Finset.range (i+1), f j := Finset.sum_le_sum hall
      _ ≤ ∑ j ∈ Finset.range M, f j := Finset.sum_le_sum_of_subset hsub
      _ = mass M f := rfl
  omega

lemma traj_supp (n t : ℕ) : Supp (traj n t) n := by
  exact supp_of_gapless_mass (traj_gapless n t) (traj_supp_succ n t) (traj_mass n t)

/-! ## Convergence -/

open Finset in
/-- Mass is independent of the range bound, as long as it covers the support. -/
lemma mass_eq_of_supp {f : ℕ → ℕ} {M K : ℕ} (h : Supp f M) (hMK : M ≤ K) :
    mass K f = mass M f := by
  unfold mass
  rw [← Finset.sum_range_add_sum_Ico f hMK]
  have : ∑ i ∈ Finset.Ico M K, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact h i hi.1
  omega

/-- Total mass over range `n`. -/
lemma traj_mass_n (n t : ℕ) : mass n (traj n t) = n := by
  rcases Nat.lt_or_ge n (t+1) with h | h
  · rw [← mass_eq_of_supp (M := n) (K := t+1) (traj_supp n t) (by omega), traj_mass]
  · rw [mass_eq_of_supp (traj_supp_succ n t) h, traj_mass]

open Finset in
/-- If all entries `≤ 1` over `[0,n)`, gapless, mass `n`, then it is the target. -/
lemma eq_target_of_all_le_one {f : ℕ → ℕ} {n : ℕ}
    (hs : Supp f n) (hm : mass n f = n) (h1 : ∀ i, i < n → f i ≤ 1) :
    f = targetf n := by
  funext i
  simp only [targetf]
  by_cases hi : i < n
  · rw [if_pos hi]
    -- show f i = 1
    have hle : f i ≤ 1 := h1 i hi
    -- and f i ≥ 1
    have hsplit : mass n f = (∑ j ∈ Finset.range n \ {i}, f j) + f i :=
      Finset.sum_eq_sum_diff_singleton_add (Finset.mem_range.mpr hi) f
    have hbound : ∑ j ∈ Finset.range n \ {i}, f j ≤ n - 1 := by
      calc ∑ j ∈ Finset.range n \ {i}, f j ≤ ∑ _j ∈ Finset.range n \ {i}, 1 := by
            apply Finset.sum_le_sum; intro j hj
            rw [Finset.mem_sdiff, Finset.mem_range] at hj
            exact h1 j hj.1
        _ = (Finset.range n \ {i}).card := by simp
        _ = n - 1 := by
            rw [← Finset.erase_eq, Finset.card_erase_of_mem (Finset.mem_range.mpr hi),
              Finset.card_range]
    omega
  · rw [if_neg hi]
    exact hs i (by omega)

open Finset in
/-- If not the target, some entry is `≥ 2`. -/
lemma exists_two_of_ne_target {n t : ℕ} (hn : 1 ≤ n)
    (hne : traj n t ≠ targetf n) : ∃ i, i < n ∧ 2 ≤ traj n t i := by
  by_contra hc
  push_neg at hc
  apply hne
  apply eq_target_of_all_le_one (traj_supp n t) (traj_mass_n n t)
  intro i hi
  have := hc i hi
  omega

open Finset in
/-- Work is positive when not at target. -/
lemma work_pos_of_ne_target {n t : ℕ} (hn : 1 ≤ n)
    (hne : traj n t ≠ targetf n) : 1 ≤ work n (traj n t) := by
  obtain ⟨i, hi, h2⟩ := exists_two_of_ne_target hn hne
  unfold work
  have hmem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  calc 1 ≤ traj n t i / 2 := by omega
    _ ≤ ∑ j ∈ Finset.range n, traj n t j / 2 :=
        Finset.single_le_sum (f := fun j => traj n t j / 2) (by intros; positivity) hmem

open Finset in
/-- Dropping the top (zero) term keeps the moment. -/
lemma mom_eq_supp {f : ℕ → ℕ} {M : ℕ} (h : Supp f M) : mom (M+1) f = mom M f := by
  unfold mom
  rw [Finset.sum_range_succ]
  rw [h M (le_refl M)]
  simp

open Finset in
/-- Moment bound. -/
lemma mom_le (n t : ℕ) : mom n (traj n t) ≤ (n-1) * n := by
  unfold mom
  calc ∑ i ∈ Finset.range n, i * traj n t i
      ≤ ∑ i ∈ Finset.range n, (n-1) * traj n t i := by
        apply Finset.sum_le_sum; intro i hi
        rw [Finset.mem_range] at hi
        apply Nat.mul_le_mul_right
        omega
    _ = (n-1) * ∑ i ∈ Finset.range n, traj n t i := by rw [Finset.mul_sum]
    _ = (n-1) * n := by rw [show ∑ i ∈ Finset.range n, traj n t i = mass n (traj n t) from rfl,
          traj_mass_n]

lemma Phi_zero (n : ℕ) : mom n (traj n 0) = 0 := by
  rw [traj_zero]
  unfold mom
  apply Finset.sum_eq_zero
  intro i _
  simp only [initf]
  by_cases hi : i = 0 <;> simp [hi]

lemma Phi_succ (n t : ℕ) :
    mom n (traj n (t+1)) = mom n (traj n t) + work n (traj n t) := by
  have h1 : mom (n+1) (traj n (t+1)) = mom n (traj n (t+1)) :=
    mom_eq_supp (traj_supp n (t+1))
  rw [← h1, traj_succ, mom_stepf (traj_supp n t)]

lemma Phi_ge {n : ℕ} (hn : 1 ≤ n) (t : ℕ)
    (h : ∀ s, s < t → traj n s ≠ targetf n) : t ≤ mom n (traj n t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht : t ≤ mom n (traj n t) := ih (fun s hs => h s (by omega))
    have hne : traj n t ≠ targetf n := h t (by omega)
    have hw : 1 ≤ work n (traj n t) := work_pos_of_ne_target hn hne
    rw [Phi_succ]
    omega

/-- The trajectory reaches the target. -/
lemma exists_hit {n : ℕ} (hn : 1 ≤ n) : ∃ t, traj n t = targetf n := by
  by_contra hc
  push_neg at hc
  have h := Phi_ge hn ((n-1)*n + 1) (fun s _ => hc s)
  have h2 := mom_le n ((n-1)*n + 1)
  omega

/-! ## Hitting time and target fixed point -/

lemma stepf_target (n : ℕ) : stepf (targetf n) = targetf n := by
  funext i
  simp only [stepf, targetf]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    by_cases hn : 0 < n <;> simp [hn]
  · rw [if_neg (show i ≠ 0 from by omega)]
    by_cases h1 : i < n
    · simp [h1, show i - 1 < n by omega]
    · rw [if_neg h1]
      by_cases h2 : i - 1 < n <;> simp [h2]

/-- Hitting time of the target (matches `sInf` from the problem statement). -/
noncomputable def A (n : ℕ) : ℕ := sInf {t | traj n t = targetf n}

lemma A_spec {n : ℕ} (hn : 1 ≤ n) : traj n (A n) = targetf n :=
  Nat.sInf_mem (exists_hit hn)

lemma A_min {n : ℕ} {t : ℕ} (h : traj n t = targetf n) : A n ≤ t :=
  Nat.sInf_le h

lemma A_lt {n : ℕ} {t : ℕ} (h : t < A n) : traj n t ≠ targetf n := by
  intro hc
  exact absurd (A_min hc) (by omega)

/-! ## Token sequence and coupling -/

/-- Token position at time `t` for the `(n+1)` vs `n` coupling. -/
def ptraj (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => pnext (traj n t) (ptraj n t)

lemma initf_succ (n : ℕ) : initf (n+1) = addE (initf n) 0 := by
  funext i
  simp only [initf, addE]
  by_cases hi : i = 0 <;> simp [hi]

/-- The coupling: the `(n+1)`-trajectory is the `n`-trajectory plus a token. -/
lemma coupling (n t : ℕ) : traj (n+1) t = addE (traj n t) (ptraj n t) := by
  induction t with
  | zero => rw [traj_zero, traj_zero, ptraj, initf_succ]
  | succ t ih =>
    rw [traj_succ, ih, step_coupling, ← traj_succ]
    rfl

lemma ptraj_succ (n t : ℕ) :
    ptraj n (t+1) = ptraj n t + traj n t (ptraj n t) % 2 := rfl

/-! ## Leading-one count -/

lemma stepf_val (f : ℕ → ℕ) (i : ℕ) :
    stepf f i = (f i + 1)/2 + (if i = 0 then 0 else f (i-1)/2) := rfl

/-- Once zero, stays zero forever (forward). -/
lemma gapless_zero_ge {f : ℕ → ℕ} (hg : Gapless f) {m : ℕ} (hm : f m = 0) :
    ∀ j, m ≤ j → f j = 0 := by
  intro j hj
  induction j with
  | zero => have : m = 0 := by omega
            rw [this] at hm; exact hm
  | succ j ih =>
    rcases Nat.lt_or_ge m (j+1) with h | h
    · exact hg j (ih (by omega))
    · have : m = j + 1 := by omega
      rw [← this]; exact hm

/-- The leading-one count. -/
noncomputable def gval (f : ℕ → ℕ) : ℕ := sInf {i | f i ≠ 1}

lemma gval_lead {f : ℕ → ℕ} {i : ℕ} (hi : i < gval f) : f i = 1 := by
  by_contra hc
  have : gval f ≤ i := Nat.sInf_le hc
  omega

lemma gval_le {f : ℕ → ℕ} {k : ℕ} (hk : f k ≠ 1) : gval f ≤ k :=
  Nat.sInf_le hk

lemma gval_mem {f : ℕ → ℕ} (h : ∃ k, f k ≠ 1) : f (gval f) ≠ 1 :=
  Nat.sInf_mem h

lemma gval_traj_le (n t : ℕ) : gval (traj n t) ≤ n :=
  gval_le (by rw [traj_supp n t n (le_refl n)]; omega)

/-- The leading-one count grows by at most 2 per step. -/
lemma gval_step_le {f : ℕ → ℕ} (hg : Gapless f) (hex : ∃ k, f k ≠ 1) :
    gval (stepf f) ≤ gval f + 2 := by
  have hfk : f (gval f) ≠ 1 := gval_mem hex
  rcases Nat.eq_zero_or_pos (f (gval f)) with h0 | hpos
  · -- f g = 0, use witness g+1
    have hk1 : f (gval f + 1) = 0 := hg (gval f) h0
    refine le_trans (gval_le (k := gval f + 1) ?_) (by omega)
    rw [stepf_val, if_neg (Nat.succ_ne_zero _)]
    simp only [Nat.add_sub_cancel, hk1, h0]; omega
  · by_cases h2 : f (gval f) = 2
    · by_cases hk10 : f (gval f + 1) = 0
      · -- shape [1^g, 2], use witness g+2
        have hk2 : f (gval f + 2) = 0 := hg (gval f + 1) hk10
        refine le_trans (gval_le (k := gval f + 2) ?_) (by omega)
        rw [stepf_val, if_neg (Nat.succ_ne_zero _),
          show gval f + 2 - 1 = gval f + 1 from by omega]
        simp only [hk2, hk10]; omega
      · -- f (g+1) ≥ 1, use witness g+1
        refine le_trans (gval_le (k := gval f + 1) ?_) (by omega)
        rw [stepf_val, if_neg (Nat.succ_ne_zero _)]
        simp only [Nat.add_sub_cancel, h2]
        omega
    · -- f g ≥ 3, use witness g
      have hge3 : 3 ≤ f (gval f) := by omega
      refine le_trans (gval_le (k := gval f) ?_) (by omega)
      rw [stepf_val]
      rcases Nat.eq_zero_or_pos (gval f) with hgz | hgp
      · rw [hgz] at hge3 ⊢; simp only [if_pos rfl]; omega
      · rw [if_neg (by omega)]; omega

/-- If the leading-one count jumps by 2, then the next config is all `≤ 1`. -/
lemma gval_jump_target {f : ℕ → ℕ} (hg : Gapless f) (hex : ∃ k, f k ≠ 1)
    (hjump : gval f + 2 ≤ gval (stepf f)) : ∀ i, stepf f i ≤ 1 := by
  have hfk : f (gval f) ≠ 1 := gval_mem hex
  -- positions gval f and gval f + 1 are leading ones of stepf f
  have hs0 : stepf f (gval f) = 1 := gval_lead (by omega)
  have hs1 : stepf f (gval f + 1) = 1 := gval_lead (by omega)
  -- derive f g = 2
  have hsec : (if gval f = 0 then 0 else f (gval f - 1) / 2) = 0 := by
    by_cases hg0 : gval f = 0
    · rw [if_pos hg0]
    · rw [if_neg hg0, gval_lead (show gval f - 1 < gval f from by omega)]
  have hfg2 : f (gval f) = 2 := by
    rw [stepf_val, hsec] at hs0
    omega
  -- derive f (g+1) = 0
  have hfg10 : f (gval f + 1) = 0 := by
    rw [stepf_val, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, hfg2] at hs1
    omega
  -- characterize f
  have hzero : ∀ j, gval f + 1 ≤ j → f j = 0 := gapless_zero_ge hg hfg10
  have hfi : ∀ j, f j = (if j < gval f then 1 else if j = gval f then 2 else 0) := by
    intro j
    by_cases hj1 : j < gval f
    · rw [if_pos hj1]; exact gval_lead hj1
    · rw [if_neg hj1]
      by_cases hj2 : j = gval f
      · rw [if_pos hj2, hj2]; exact hfg2
      · rw [if_neg hj2]; exact hzero j (by omega)
  intro i
  rw [stepf_val]
  have e1 := hfi i
  have e2 := hfi (i - 1)
  split_ifs at e1 e2 ⊢ <;> omega

/-- If next config jumps `gval` by 2, the +1 bound fails; so for non-jumps it holds. -/
lemma gval_step_le_one {f : ℕ → ℕ} (hg : Gapless f) (hex : ∃ k, f k ≠ 1)
    (hnotall : ¬ ∀ i, stepf f i ≤ 1) : gval (stepf f) ≤ gval f + 1 := by
  rcases Nat.lt_or_ge (gval f + 1) (gval (stepf f)) with h | h
  · exact absurd (gval_jump_target hg hex (by omega)) hnotall
  · omega

/-- Existence witness for `gval` of `traj`. -/
lemma traj_hex (n t : ℕ) : ∃ k, traj n t k ≠ 1 :=
  ⟨n, by rw [traj_supp n t n (le_refl n)]; omega⟩

/-- Non-target configs are not all `≤ 1`. -/
lemma not_all_le_one {n t : ℕ} (hne : traj n t ≠ targetf n) :
    ¬ ∀ i, traj n t i ≤ 1 := by
  intro hall
  exact hne (eq_target_of_all_le_one (traj_supp n t) (traj_mass_n n t) (fun i _ => hall i))

/-! ## Invariant K: the token stays within 1 of the leading-one front -/

lemma Kinv {n : ℕ} : ∀ t, traj n t ≠ targetf n →
    gval (traj n t) ≤ ptraj n t + 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [traj_zero, ptraj]
    exact gval_le (by simp [initf])
  | succ t ih =>
    intro hne
    -- traj n t is non-terminal
    have hnet : traj n t ≠ targetf n := by
      intro hc
      apply hne
      rw [traj_succ, hc, stepf_target]
    have hIH : gval (traj n t) ≤ ptraj n t + 1 := ih hnet
    -- gval grows by at most 1
    have hnotall : ¬ ∀ i, stepf (traj n t) i ≤ 1 := by
      rw [← traj_succ]; exact not_all_le_one hne
    have hle1 : gval (traj n (t+1)) ≤ gval (traj n t) + 1 := by
      rw [traj_succ]
      exact gval_step_le_one (traj_gapless n t) (traj_hex n t) hnotall
    rw [ptraj_succ]
    rcases Nat.lt_or_ge (ptraj n t) (gval (traj n t)) with hpg | hpg
    · -- token inside leading run: it moves
      have hone : traj n t (ptraj n t) = 1 := gval_lead hpg
      rw [hone]
      omega
    · -- token at/ahead of front
      omega

/-! ## Auxiliary target/gval lemmas -/

lemma gval_target (n : ℕ) : gval (targetf n) = n := by
  apply le_antisymm
  · apply gval_le; simp [targetf]
  · by_contra hc
    push_neg at hc
    have hmem := gval_mem (⟨n, by simp [targetf]⟩ : ∃ k, targetf n k ≠ 1)
    have h1 : targetf n (gval (targetf n)) = 1 := by
      simp only [targetf]; rw [if_pos hc]
    exact hmem h1

open Finset in
lemma all_ge_one_target {n t : ℕ} (h : ∀ i, i < n → 1 ≤ traj n t i) :
    traj n t = targetf n := by
  apply eq_target_of_all_le_one (traj_supp n t) (traj_mass_n n t)
  intro i hi
  by_contra hc
  push_neg at hc
  have hsplit : mass n (traj n t) = (∑ j ∈ Finset.range n \ {i}, traj n t j) + traj n t i :=
    Finset.sum_eq_sum_diff_singleton_add (Finset.mem_range.mpr hi) _
  have hge : (n - 1) ≤ ∑ j ∈ Finset.range n \ {i}, traj n t j := by
    calc n - 1 = (Finset.range n \ {i}).card := by
            rw [← Finset.erase_eq, Finset.card_erase_of_mem (Finset.mem_range.mpr hi),
              Finset.card_range]
      _ = ∑ _j ∈ Finset.range n \ {i}, 1 := by simp
      _ ≤ ∑ j ∈ Finset.range n \ {i}, traj n t j := by
            apply Finset.sum_le_sum; intro j hj
            rw [Finset.mem_sdiff, Finset.mem_range] at hj
            exact h j hj.1
  have hm := traj_mass_n n t
  omega

lemma traj_last_le {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : traj n t (n-1) ≤ 1 := by
  have h0 : traj n (t+1) n = 0 := traj_supp n (t+1) n (le_refl n)
  rw [traj_succ n t, stepf_val (traj n t) n, if_neg (show n ≠ 0 by omega)] at h0
  have hn0 : traj n t n = 0 := traj_supp n t n (le_refl n)
  rw [hn0] at h0
  omega

lemma traj_last_one_target {n t : ℕ} (hn : 1 ≤ n) (h : traj n t (n-1) = 1) :
    traj n t = targetf n := by
  apply all_ge_one_target
  intro i hi
  have hne : traj n t (n-1) ≠ 0 := by rw [h]; omega
  have := gapless_down (traj_gapless n t) (n-1) i (by omega) hne
  omega

lemma addE_self (f : ℕ → ℕ) (p : ℕ) : addE f p p = f p + 1 := by
  simp [addE]

lemma addE_of_ne (f : ℕ → ℕ) {p i : ℕ} (h : i ≠ p) : addE f p i = f i := by
  simp [addE, h]

lemma targetf_eval (n i : ℕ) : targetf n i = if i < n then 1 else 0 := rfl

lemma ptraj_lt_n {n t : ℕ} (hn : 1 ≤ n) (hne : traj n t ≠ targetf n) :
    ptraj n t < n := by
  have hgap : Gapless (traj (n+1) t) := traj_gapless (n+1) t
  rw [coupling] at hgap
  have hple : ptraj n t ≤ n := by
    by_contra hc
    push_neg at hc
    have hz : addE (traj n t) (ptraj n t) n = 0 := by
      rw [addE_of_ne (traj n t) (show n ≠ ptraj n t by omega)]
      exact traj_supp n t n (le_refl n)
    have hzz := gapless_zero_ge hgap hz (ptraj n t) (by omega)
    rw [addE_self] at hzz
    omega
  rcases Nat.lt_or_ge (ptraj n t) n with h | h
  · exact h
  · exfalso
    have hpn : ptraj n t = n := by omega
    apply hne
    apply all_ge_one_target
    intro i hi
    have hne0 : addE (traj n t) (ptraj n t) n ≠ 0 := by
      have he : addE (traj n t) (ptraj n t) n = traj n t n + 1 := by
        rw [hpn]; exact addE_self (traj n t) n
      rw [he]; omega
    have hdn := gapless_down hgap n i (by omega) hne0
    have heq : addE (traj n t) (ptraj n t) i = traj n t i :=
      addE_of_ne (traj n t) (show i ≠ ptraj n t by omega)
    rw [heq] at hdn
    omega

lemma ptraj_A_le {n : ℕ} (hn : 1 ≤ n) : ptraj n (A n) ≤ n - 1 := by
  rcases Nat.eq_zero_or_pos (A n) with hA | hA
  · rw [hA]; simp only [ptraj]; omega
  · obtain ⟨m, hm⟩ : ∃ m, A n = m + 1 := ⟨A n - 1, by omega⟩
    rw [hm]
    have hmlt : m < A n := by omega
    have hne : traj n m ≠ targetf n := A_lt hmlt
    have hp : ptraj n m < n := ptraj_lt_n hn hne
    rw [ptraj_succ]
    rcases Nat.lt_or_ge (ptraj n m) (n-1) with h | h
    · omega
    · have hpn1 : ptraj n m = n - 1 := by omega
      rw [hpn1]
      have hlast := traj_last_le hn m
      have h0 : traj n m (n-1) = 0 := by
        rcases Nat.lt_or_ge (traj n m (n-1)) 1 with h1 | h1
        · omega
        · exact absurd (traj_last_one_target hn (by omega)) hne
      rw [h0]; omega

lemma ptraj_A_ge {n : ℕ} (hn : 1 ≤ n) : n ≤ ptraj n (A n) + 2 := by
  rcases Nat.eq_zero_or_pos (A n) with hA | hA
  · have h0 : traj n 0 = targetf n := by rw [← hA]; exact A_spec hn
    rw [traj_zero] at h0
    have hval : n = 1 := by
      have hh : initf n 0 = targetf n 0 := by rw [h0]
      have e1 : initf n 0 = n := by simp [initf]
      have e2 : targetf n 0 = 1 := by rw [targetf_eval, if_pos (show 0 < n by omega)]
      rw [e1, e2] at hh; omega
    omega
  · obtain ⟨m, hm⟩ : ∃ m, A n = m + 1 := ⟨A n - 1, by omega⟩
    have hmlt : m < A n := by omega
    have hne : traj n m ≠ targetf n := A_lt hmlt
    have hstep : stepf (traj n m) = targetf n := by
      rw [← traj_succ, ← hm]; exact A_spec hn
    have hgt : gval (stepf (traj n m)) = n := by rw [hstep]; exact gval_target n
    have hg2 : n ≤ gval (traj n m) + 2 := by
      have := gval_step_le (traj_gapless n m) (traj_hex n m)
      omega
    have hge : gval (traj n m) ≤ ptraj n (A n) := by
      rw [hm, ptraj_succ]
      rcases Nat.lt_or_ge (ptraj n m) (gval (traj n m)) with h | h
      · have hone : traj n m (ptraj n m) = 1 := gval_lead h
        rw [hone]
        have hk := Kinv m hne
        omega
      · omega
    omega

/-! ## The "two walks right" identity and the recurrence for A -/

lemma stepf_addE_target (n p : ℕ) :
    stepf (addE (targetf n) p) = addE (targetf n) (p + (if p < n then 1 else 0)) := by
  rw [step_coupling, stepf_target]
  congr 1
  simp only [pnext, targetf]
  by_cases h : p < n <;> simp [h]

lemma addE_target_succ (n : ℕ) : addE (targetf n) n = targetf (n+1) := by
  funext i
  simp only [addE, targetf]
  rcases Nat.lt_trichotomy i n with h | h | h
  · rw [if_pos h, if_neg (by omega), if_pos (by omega)]
  · subst h; rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma walk_target (n p : ℕ) : ∀ s, p + s ≤ n →
    (stepf)^[s] (addE (targetf n) p) = addE (targetf n) (p + s) := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hps
    rw [Function.iterate_succ', Function.comp_apply, ih (by omega), stepf_addE_target,
        if_pos (show p + s < n by omega), Nat.add_assoc]

lemma traj_add (n a b : ℕ) : traj n (a + b) = (stepf)^[a] (traj n b) := by
  simp only [traj, Function.iterate_add_apply]

lemma coupling_target {n s : ℕ} (hn : 1 ≤ n)
    (h : traj (n+1) s = targetf (n+1)) : traj n s = targetf n := by
  rw [coupling] at h
  set q := ptraj n s with hq
  have hqval : traj n s q + 1 = targetf (n+1) q := by
    have hcq := congrFun h q; rw [addE_self] at hcq; exact hcq
  have hqle : q ≤ n := by
    by_contra hc
    push_neg at hc
    rw [targetf_eval, if_neg (show ¬ q < n+1 by omega)] at hqval
    omega
  have hqn : q = n := by
    by_contra hc
    have hqlt : q < n := by omega
    have htq : traj n s q = 0 := by
      rw [targetf_eval, if_pos (show q < n+1 by omega)] at hqval
      omega
    have hg := traj_gapless n s q htq
    have hc2 := congrFun h (q+1)
    rw [addE_of_ne (traj n s) (show q+1 ≠ q by omega), targetf_eval,
        if_pos (show q+1 < n+1 by omega)] at hc2
    omega
  rw [hqn] at h
  funext i
  have hi := congrFun h i
  by_cases h1 : i < n
  · rw [addE_of_ne (traj n s) (show i ≠ n by omega), targetf_eval,
        if_pos (show i < n+1 by omega)] at hi
    rw [targetf_eval, if_pos h1]
    omega
  · by_cases h2 : i = n
    · rw [h2, addE_self, targetf_eval, if_pos (show n < n+1 by omega)] at hi
      rw [h2, targetf_eval, if_neg (show ¬ n < n by omega)]
      omega
    · rw [addE_of_ne (traj n s) (show i ≠ n by omega), targetf_eval,
          if_neg (show ¬ i < n+1 by omega)] at hi
      rw [targetf_eval, if_neg (show ¬ i < n by omega)]
      omega

lemma A_succ {n : ℕ} (hn : 1 ≤ n) :
    A (n+1) = A n + (n - ptraj n (A n)) := by
  set p := ptraj n (A n) with hp
  have hpn : p ≤ n := le_trans (ptraj_A_le hn) (by omega)
  have hbase : traj (n+1) (A n) = addE (targetf n) p := by
    rw [coupling, A_spec hn]
  have hd : p + (n - p) = n := by omega
  have hupper : A (n+1) ≤ A n + (n - p) := by
    apply A_min
    rw [show A n + (n - p) = (n - p) + A n by omega, traj_add, hbase,
        walk_target n p (n-p) (by omega), hd, addE_target_succ]
  have hlower : A n + (n - p) ≤ A (n+1) := by
    by_contra hc
    push_neg at hc
    have hspec : traj (n+1) (A (n+1)) = targetf (n+1) := A_spec (by omega)
    rcases Nat.lt_or_ge (A (n+1)) (A n) with hcase | hcase
    · exact (A_lt hcase) (coupling_target hn hspec)
    · obtain ⟨s', hs'⟩ : ∃ s', A (n+1) = A n + s' := ⟨A (n+1) - A n, by omega⟩
      have hs'lt : s' < n - p := by omega
      have hval : traj (n+1) (A (n+1)) = addE (targetf n) (p + s') := by
        rw [hs', show A n + s' = s' + A n by omega, traj_add, hbase,
            walk_target n p s' (by omega)]
      rw [hval] at hspec
      have hcontra := congrFun hspec (p + s')
      rw [addE_self, targetf_eval, if_pos (show p + s' < n by omega),
          targetf_eval, if_pos (show p + s' < n+1 by omega)] at hcontra
      omega
  omega

lemma A_diff {n : ℕ} (hn : 1 ≤ n) :
    A (n+1) = A n + 1 ∨ A (n+1) = A n + 2 := by
  have hfor := A_succ hn
  have hle := ptraj_A_le hn
  have hge := ptraj_A_ge hn
  omega

/-! ## Bridge: the list-based definition `a` equals `A` -/

open List

noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2
  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse
  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor
    let next_config_long := List.zipWith Nat.add base_masses received_masses
    trim_trailing_zeros next_config_long
  if n = 0 then 0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config
    let stable_steps : Set ℕ := {k | S k = target_config}
    sInf stable_steps

def trimz (l : List ℕ) : List ℕ := (l.reverse.dropWhile (fun x => x = 0)).reverse

def nextLong (l : List ℕ) : List ℕ :=
  List.zipWith Nat.add (l.map (fun m => (m+1)/2) ++ [0]) (0 :: l.map (fun m => m/2))

def caStep (l : List ℕ) : List ℕ := trimz (nextLong l)

theorem getD_append_zero (l : List ℕ) (i : ℕ) : (l ++ [0]).getD i 0 = l.getD i 0 := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_append l [0] 0 i h]
  · rw [List.getD_append_right l [0] 0 i h]
    have hr : l.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h, Option.getD_none]
    rw [hr]
    rcases Nat.eq_or_lt_of_le h with he | hlt
    · rw [show i - l.length = 0 by omega]; rfl
    · have h2 : ([0]:List ℕ).getD (i - l.length) 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by simp; omega),
            Option.getD_none]
      rw [h2]

theorem repr_trimz (l : List ℕ) : ∀ i, (trimz l).getD i 0 = l.getD i 0 := by
  induction l using List.reverseRecOn with
  | nil => intro i; rfl
  | append_singleton l' x ih =>
    intro i
    by_cases hx : x = 0
    · subst hx
      have ht : trimz (l' ++ [0]) = trimz l' := by
        simp only [trimz, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append]
        simp
      rw [ht, ih, getD_append_zero]
    · have hrev : (l' ++ [x]).reverse = x :: l'.reverse := by simp
      have ht : trimz (l' ++ [x]) = l' ++ [x] := by
        simp only [trimz, hrev, List.dropWhile_cons]
        rw [if_neg (by simp [hx])]
        simp
      rw [ht]

theorem map_getD {α β} (f : α → β) (l : List α) (i : ℕ) (d : α) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem getD_single_zero (j : ℕ) : ([0]:List ℕ).getD j 0 = 0 := by
  rcases j with _ | j
  · rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by simp)]; rfl

theorem zipWith_add_getD (a b : List ℕ) (hlen : a.length = b.length) (i : ℕ) :
    (List.zipWith Nat.add a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i a.length with h | h
  · rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (show i < b.length by omega)]
    simp
  · rw [List.getElem?_eq_none_iff.mpr h, List.getElem?_eq_none_iff.mpr (show b.length ≤ i by omega)]
    simp

theorem base_getD (l : List ℕ) (i : ℕ) :
    (l.map (fun m => (m+1)/2) ++ [0]).getD i 0 = (l.getD i 0 + 1)/2 := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact map_getD (fun m => (m+1)/2) l i 0
  · have hr : l.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h, Option.getD_none]
    rw [List.getD_append_right (l.map (fun m => (m+1)/2)) [0] 0 i (by simpa using h), hr,
        getD_single_zero]

theorem recv_getD (l : List ℕ) (i : ℕ) :
    (0 :: l.map (fun m => m/2)).getD i 0 = if i = 0 then 0 else l.getD (i-1) 0 / 2 := by
  rcases i with _ | j
  · rfl
  · rw [List.getD_cons_succ]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    exact map_getD (fun m => m/2) l j 0

theorem repr_nextLong (l : List ℕ) (i : ℕ) :
    (nextLong l).getD i 0 = stepf (fun j => l.getD j 0) i := by
  rw [nextLong, zipWith_add_getD _ _ (by simp), base_getD, recv_getD]
  rfl

theorem repr_caStep (l : List ℕ) (i : ℕ) :
    (caStep l).getD i 0 = stepf (fun j => l.getD j 0) i := by
  rw [caStep, repr_trimz, repr_nextLong]

theorem foldl_range_iterate {α} (g : α → α) (k : ℕ) (init : α) :
    (List.range k).foldl (fun acc _ => g acc) init = g^[k] init := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ']
    rfl

theorem repr_iterate (l : List ℕ) (t : ℕ) :
    (fun i => (caStep^[t] l).getD i 0) = stepf^[t] (fun i => l.getD i 0) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [← ih]
    funext i
    exact repr_caStep (caStep^[t] l) i

theorem repr_single (n : ℕ) : (fun i => ([n] : List ℕ).getD i 0) = initf n := by
  funext i
  rcases i with _ | i
  · rfl
  · rw [List.getD_cons_succ]; simp [initf]

theorem repr_S_eq (n t : ℕ) :
    (fun i => (caStep^[t] [n]).getD i 0) = traj n t := by
  rw [repr_iterate, repr_single]; rfl

theorem repr_replicate (n i : ℕ) :
    (List.replicate n 1).getD i 0 = if i < n then 1 else 0 := by
  rcases Nat.lt_or_ge i n with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_replicate, if_pos h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (by simpa using h),
        Option.getD_none, if_neg (by omega)]

theorem trimz_last_ne (a' : List ℕ) (x : ℕ) (h : trimz (a' ++ [x]) = a' ++ [x]) : x ≠ 0 := by
  intro hx
  subst hx
  have ht : trimz (a' ++ [0]) = trimz a' := by
    simp only [trimz, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append]
    simp
  rw [ht] at h
  have e := congrArg List.length h
  have hle : (trimz a').length ≤ a'.length := by
    simp only [trimz, List.length_reverse]
    exact (List.length_dropWhile_le _ _).trans (by simp)
  simp only [List.length_append, List.length_cons, List.length_nil] at e
  omega

theorem trimz_len_le (a : List ℕ) (ha : trimz a = a) (m : ℕ)
    (hm : ∀ i, m ≤ i → a.getD i 0 = 0) : a.length ≤ m := by
  by_contra hc
  push_neg at hc
  rcases List.eq_nil_or_concat a with hnil | ⟨a', x, rfl⟩
  · rw [hnil] at hc; simp at hc
  · simp only [List.concat_eq_append] at ha hm hc ⊢
    have hlen : (a' ++ [x]).length = a'.length + 1 := by simp
    have hx : x ≠ 0 := trimz_last_ne a' x ha
    have hval : (a' ++ [x]).getD a'.length 0 = x := by
      rw [List.getD_append_right a' [x] 0 a'.length (le_refl _)]; simp
    have hz := hm a'.length (by omega)
    rw [hval] at hz
    exact hx hz

theorem eq_of_trimz_repr (a b : List ℕ) (ha : trimz a = a) (hb : trimz b = b)
    (h : ∀ i, a.getD i 0 = b.getD i 0) : a = b := by
  have hab : a.length ≤ b.length := by
    apply trimz_len_le a ha
    intro i hi
    rw [h i, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hi, Option.getD_none]
  have hba : b.length ≤ a.length := by
    apply trimz_len_le b hb
    intro i hi
    rw [← h i, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hi, Option.getD_none]
  apply List.ext_getElem (by omega)
  intro i h1 h2
  have := h i
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact this

theorem trimz_caStep (l : List ℕ) : trimz (caStep l) = caStep l := by
  simp only [caStep, trimz, List.reverse_reverse, List.dropWhile_idempotent]

theorem S_trimmed (n : ℕ) (hn : 1 ≤ n) : ∀ t, trimz (caStep^[t] [n]) = caStep^[t] [n]
  | 0 => by
    simp only [Function.iterate_zero, id_eq, trimz, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.dropWhile_cons]
    rw [if_neg (by simp; omega)]
    simp
  | t+1 => by
    rw [Function.iterate_succ', Function.comp_apply]
    exact trimz_caStep _

theorem trimz_replicate (n : ℕ) (hn : 1 ≤ n) :
    trimz (List.replicate n 1) = List.replicate n 1 := by
  have hrev : (List.replicate n 1).reverse = List.replicate n 1 := by simp
  rw [trimz, hrev]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  rw [List.replicate_succ, List.dropWhile_cons, if_neg (by simp)]
  rw [List.reverse_cons, List.reverse_replicate]
  exact List.replicate_succ'.symm

theorem S_eq_target_iff (n : ℕ) (hn : 1 ≤ n) (t : ℕ) :
    (List.range t).foldl (fun acc _ => caStep acc) [n] = List.replicate n 1
      ↔ traj n t = targetf n := by
  rw [foldl_range_iterate]
  constructor
  · intro hS
    have key := repr_S_eq n t
    rw [hS] at key
    rw [← key]
    funext i; rw [repr_replicate, targetf_eval]
  · intro hT
    apply eq_of_trimz_repr _ _ (S_trimmed n hn t) (trimz_replicate n hn)
    intro i
    have e1 : (caStep^[t] [n]).getD i 0 = traj n t i := congrFun (repr_S_eq n t) i
    have e2 : (List.replicate n 1).getD i 0 = targetf n i := by rw [repr_replicate, targetf_eval]
    rw [e1, e2, hT]

theorem a_eq_A (n : ℕ) (hn : 1 ≤ n) : a n = A n := by
  have hne : n ≠ 0 := by omega
  have ha : a n = sInf {k | (List.range k).foldl (fun acc _ => caStep acc) [n]
      = List.replicate n 1} := by
    unfold a; simp only [hne, if_false]; rfl
  rw [ha, A]
  congr 1
  ext k
  exact S_eq_target_iff n hn k

theorem main_thm : ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  rw [a_eq_A n hn, a_eq_A (n+1) (by omega)]
  exact A_diff hn
