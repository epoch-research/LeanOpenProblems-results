import Submission.Cong2

open Nat Int Finset BigOperators

def A361711 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n_ge_2 =>
    let N := n_ge_2
    let m : ℕ := N - 2
    (Finset.range (m + 1)).sum fun k : ℕ =>
      let term_nat : ℕ := (N.choose k) * (N.choose k) * (m.choose k)
      let sign_k : ℤ := (-1 : ℤ) ^ k
      sign_k * term_nat.cast

theorem hAnat (n : ℕ) (hn : 2 ≤ n) : (A361711 n : ℚ) = aaq n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have hA : A361711 (j+2) = (Finset.range (j+1)).sum
      (fun k : ℕ => (-1:ℤ)^k * (((j+2).choose k)*((j+2).choose k)*(j.choose k) : ℕ)) := rfl
  rw [hA]; push_cast
  rw [aaq]
  rw [← Finset.sum_subset (s₁ := Finset.range (j+1)) (s₂ := Finset.range (j+2+1))
        (by intro x hx; rw [Finset.mem_range] at *; omega)
        (fun x _ hx => Fq_zero (j+2) x (by simp only [Finset.mem_range, not_lt] at hx; omega))]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Fq]
  rw [show (j+2)-2 = j from rfl]
  push_cast; ring

theorem hA_odd (m : ℕ) : A361711 (2*m+1) = Aint m := by
  rcases Nat.eq_zero_or_pos m with h|h
  · subst h; rfl
  · have hge : 2 ≤ 2*m+1 := by omega
    have h1 := hAnat (2*m+1) hge
    have hcast : ((A361711 (2*m+1):ℤ):ℚ) = ((Aint m:ℤ):ℚ) := by
      rw [h1, closedform m, Aint_cast m]
    exact_mod_cast hcast

theorem A361711_conjecture (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  set M := (p^k - 1)/2 with hMdef
  have hMk : 2*M+1 = p^k := by
    have : (p^k) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    rw [hMdef]; omega
  set M' := (p^(k-1) - 1)/2 with hM'def
  have hM'k : 2*M'+1 = p^(k-1) := by
    have : (p^(k-1)) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    rw [hM'def]; omega
  set d := (p-1)/2 with hddef
  have hd : 2*d+1 = p := by
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    rw [hddef]; omega
  have e1 : p * (2*M'+1) = p^k := by rw [hM'k, ← pow_succ']; congr 1; omega
  have hMM' : M = p*M' + d := by
    have e2 : 2*(p*M'+d)+1 = 2*M+1 := by rw [hMk, ← e1, ← hd]; ring
    omega
  have hcore := core_dvd p k M M' d hp h_geq_5 (by omega) hMk hM'k hd hMM'
  have hAk : A361711 (p^k) = Aint M := by rw [← hMk]; exact hA_odd M
  have hAk1 : A361711 (p^(k-1)) = Aint M' := by rw [← hM'k]; exact hA_odd M'
  rw [hAk, hAk1, Int.modEq_iff_dvd]
  have hcast : ((p^(3*k):ℕ):ℤ) = (p:ℤ)^(3*k) := by push_cast; ring
  rw [hcast, show Aint M' - Aint M = -(Aint M - Aint M') from by ring]
  exact dvd_neg.mpr hcore
