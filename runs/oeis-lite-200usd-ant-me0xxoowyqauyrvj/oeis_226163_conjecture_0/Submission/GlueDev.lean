import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

namespace GlueDev

noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  M.det

-- stubs of the two directions
theorem easy_direction (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (m : ℕ) (hm : m = (p-1)/2) (Mtx : Matrix (Fin m) (Fin m) ℤ)
    (hM : Mtx = fun i j => jacobiSym
      (((i.val+1 : ℕ) : ℤ) * ((i.val+1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val+1 : ℕ) : ℤ)) p) :
    Mtx.det ≠ 0 := sorry

theorem hard_direction (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3)
    (m : ℕ) (hm : m = (p-1)/2) (Mtx : Matrix (Fin m) (Fin m) ℤ)
    (hM : Mtx = fun i j => jacobiSym
      (((i.val+1 : ℕ) : ℤ) * ((i.val+1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val+1 : ℕ) : ℤ)) p) :
    Mtx.det = 0 := sorry

theorem conjecture (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  set p := Nat.nth Nat.Prime (n-1) with hpdef
  have hsetinf : {q | Nat.Prime q}.Infinite := by
    simpa only [Nat.prime_iff] using Nat.infinite_setOf_prime
  have hp : p.Prime := Nat.nth_mem_of_infinite hsetinf (n-1)
  have hp3 : 3 ≤ p := by
    have h1 : (1:ℕ) ≤ n-1 := by omega
    have h2 : Nat.nth Nat.Prime 1 ≤ p :=
      (Nat.nth_strictMono hsetinf).monotone h1
    rw [Nat.nth_prime_one_eq_three] at h2
    exact h2
  set m : ℕ := (p - 1) / 2 with hmdef
  set Mtx : Matrix (Fin m) (Fin m) ℤ := fun i j => jacobiSym
      (((i.val+1 : ℕ) : ℤ) * ((i.val+1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val+1 : ℕ) : ℤ)) p with hMtxdef
  have hA : A226163 n = Mtx.det := by
    rw [A226163, dif_neg (by omega : ¬ n < 2)]
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rw [hA]
  constructor
  · intro hdet
    by_contra hne
    have h1 : p % 4 = 1 := by omega
    exact easy_direction p hp h1 m rfl Mtx hMtxdef hdet
  · intro h3
    exact hard_direction p hp h3 m rfl Mtx hMtxdef

end GlueDev
