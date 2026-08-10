import FormalConjectures.Util.ProblemImports

open Finset Nat

def non_p_part (p x : ℕ) : ℕ := x / p^(padicValNat p x)

def G (p : ℕ) (S : Finset ℕ) (y : ℕ) : Finset ℕ :=
  S.filter (fun x => non_p_part p x = y)

lemma G_disjoint (p : ℕ) (S : Finset ℕ) (y1 y2 : ℕ) (h : y1 ≠ y2) :
    Disjoint (G p S y1) (G p S y2) := by
  rw [disjoint_iff_ne]
  intro a ha b hb
  dsimp [G] at ha hb
  simp only [mem_filter] at ha hb
  intro heq
  rw [heq] at ha
  exact h (ha.2.symm.trans hb.2)

lemma closed_contradiction (n : ℕ) (p : ℕ) (hp : Nat.Prime p) (hpn : p ≤ n)
    (s : Finset ℕ) (hs : s ⊆ Icc 1 n) (hp_mem : p ∈ s) (h_closed : ∀ x ∈ s, p * x ≤ n → p * x ∈ s)
    (h_gt : p^(min_h n p hp hpn s hs hp_mem) > n) (a : ℕ) (ha : a ≥ 1) :
    p^a * s.prod id ∉ products n := by
  intro hpa
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  have h_s_ne : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have hx' := hs hx
    rw [mem_Icc] at hx'
    omega
  have h_non_p_s : non_p_part p (s.prod id) = s.prod (fun x => non_p_part p x) :=
    non_p_part_prod p s h_s_ne
  dsimp [products] at hpa
  rw [mem_image] at hpa
  rcases hpa with ⟨s2, hs2, h_prod2⟩
  rw [mem_powerset] at hs2
  have h_s2_ne : ∀ x ∈ s2, x ≠ 0 := by
    intro x hx
    have hx' := hs2 hx
    rw [mem_Icc] at hx'
    omega
  have h_non_p_s2 : non_p_part p (s2.prod id) = s2.prod (fun x => non_p_part p x) :=
    non_p_part_prod p s2 h_s2_ne
  have h_prod_eq : s2.prod id = p^a * s.prod id := h_prod2.symm
  have h_non_p_eq : non_p_part p (s2.prod id) = non_p_part p (s.prod id) := by
    rw [h_prod_eq]
    have h_prod_ne : s.prod id ≠ 0 := by
      apply prod_ne_zero_iff.2
      intro x hx
      exact h_s_ne x hx
    exact non_p_part_mul_p_pow p (s.prod id) a h_prod_ne
  have h_prod_non_p_eq : s2.prod (fun x => non_p_part p x) = s.prod (fun x => non_p_part p x) := by
    rw [← h_non_p_s2, h_non_p_eq, h_non_p_s]
  -- Now we have s2.prod ... = s.prod ...
  -- Can we show s2.prod id ≤ s.prod id?
  sorry




