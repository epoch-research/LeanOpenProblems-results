import FormalConjectures.Util.ProblemImports
open Finset Nat Set

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | A047983_count m = n}

/-- counting function of tau4 numbers below x -/
noncomputable def g4 (x : ℕ) : ℕ := ((Finset.Ico 1 x).filter (fun k => tau k = 4)).card

theorem tau_prime {p : ℕ} (hp : p.Prime) : tau p = 2 := by
  unfold tau; rw [Nat.Prime.divisors hp]
  have h1p : (1 : ℕ) ≠ p := fun h => hp.ne_one h.symm
  rw [Finset.card_pair h1p]

/-- KEY analytic inequality (to be proven). -/
theorem key (p : ℕ) (hp : p.Prime) (h31 : 31 < p) :
    ((Finset.Ico 1 p).filter (fun k => tau k = 2)).card + 1 ≤ g4 p := by
  sorry

theorem g4_zero : g4 0 = 0 := by simp [g4]
theorem g4_one : g4 1 = 0 := by simp [g4]

theorem Ico_one_succ (x : ℕ) (hx : 1 ≤ x) :
    Finset.Ico 1 (x + 1) = insert x (Finset.Ico 1 x) := by
  ext y; simp only [Finset.mem_Ico, Finset.mem_insert]; omega

theorem g4_succ (x : ℕ) (hx : 1 ≤ x) :
    g4 (x + 1) = g4 x + (if tau x = 4 then 1 else 0) := by
  unfold g4
  rw [Ico_one_succ x hx, Finset.filter_insert]
  by_cases h : tau x = 4
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, add_zero]

theorem g4_le_succ (x : ℕ) : g4 x ≤ g4 (x + 1) := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; rw [g4_zero, g4_one]
  · rw [g4_succ x h]; omega

/-- Discrete IVT: if g4 p ≥ N+1 then there is a tau4 number m < p with g4 m = N. -/
theorem exists_g4_eq {p N : ℕ} (hp : 1 ≤ p) (h : N + 1 ≤ g4 p) :
    ∃ m, 1 ≤ m ∧ m < p ∧ tau m = 4 ∧ g4 m = N := by
  have hex : ∃ x, N + 1 ≤ g4 x := ⟨p, h⟩
  set x0 := Nat.find hex with hx0def
  have hx0 : N + 1 ≤ g4 x0 := Nat.find_spec hex
  have hx0le : x0 ≤ p := Nat.find_le h
  have hne0 : x0 ≠ 0 := by
    intro hc; rw [hc, g4_zero] at hx0; omega
  have hne1 : x0 ≠ 1 := by
    intro hc; rw [hc, g4_one] at hx0; omega
  have hx0ge2 : 2 ≤ x0 := by omega
  set m := x0 - 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmx0 : m + 1 = x0 := by omega
  have hlt : m < x0 := by omega
  have hnm : ¬ (N + 1 ≤ g4 m) := Nat.find_min hex hlt
  have hgm : g4 m ≤ N := by omega
  have hgsucc : g4 (m + 1) = g4 m + (if tau m = 4 then 1 else 0) := g4_succ m hm1
  rw [hmx0] at hgsucc
  refine ⟨m, hm1, by omega, ?_, ?_⟩
  · by_contra htau
    rw [if_neg htau, add_zero] at hgsucc
    rw [hgsucc] at hx0; omega
  · rw [if_pos ?_] at hgsucc
    · omega
    · by_contra htau
      rw [if_neg htau, add_zero] at hgsucc
      rw [hgsucc] at hx0; omega

theorem foo_disproof : ¬ (∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31) := by
  rintro ⟨n, hn, hp, h31⟩
  set p := a n with hpdef
  have hSne : {m : ℕ | A047983_count m = n}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : a n = 0 := by unfold a; rw [h]; exact Nat.sInf_empty
    omega
  have hmem : p ∈ {m : ℕ | A047983_count m = n} := Nat.sInf_mem hSne
  have hcount : A047983_count p = n := hmem
  have htaup : tau p = 2 := tau_prime hp
  have hg2 : ((Finset.Ico 1 p).filter (fun k => tau k = 2)).card = n := by
    have : A047983_count p = ((Finset.Ico 1 p).filter (fun k => tau k = 2)).card := by
      unfold A047983_count; simp only [htaup]
    rw [← this]; exact hcount
  have hkey := key p hp h31
  rw [hg2] at hkey
  obtain ⟨m, hm1, hmp, hmt, hmg⟩ := exists_g4_eq (by omega : 1 ≤ p) hkey
  have hmcount : A047983_count m = n := by
    unfold A047983_count; simp only [hmt]
    rw [show ((Finset.Ico 1 m).filter (fun k => tau k = 4)).card = g4 m from rfl, hmg]
  have hmS : m ∈ {m : ℕ | A047983_count m = n} := hmcount
  have : p ≤ m := Nat.sInf_le hmS
  omega
