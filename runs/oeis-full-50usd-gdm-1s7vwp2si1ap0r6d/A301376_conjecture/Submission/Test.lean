import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )


lemma a_pos_of_exists (n : ℕ) (x y z w : ℕ) (k : ℕ)
    (h_sum : x^2 + y^2 + z^2 + w^2 = n^2)
    (h_le : z ≤ w)
    (h_pell : (x : ℤ)^2 - (3 * (y : ℤ))^2 = (4^k : ℤ))
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n) (hk : k ≤ n) : a n > 0 := by
  unfold a
  apply Finset.card_pos.mpr
  use ((x, y), (z, w))
  simp
  refine ⟨⟨⟨hx, hy⟩, hz, hw⟩, h_sum, h_le, k, hk, h_pell⟩

-- Lemma to reduce even numbers
lemma a_even (m : ℕ) (h : a m > 0) : a (2 * m) > 0 := by
  have hm : m > 0 := by
    by_contra hc
    have : m = 0 := by omega
    subst this
    revert h
    decide
  unfold a at h
  rcases Finset.card_pos.mp h with ⟨p, hp⟩
  simp at hp
  rcases hp with ⟨⟨⟨hx, hy⟩, hz, hw⟩, h_sum, h_le, k, hk, hk_eq⟩
  set x := p.1.1
  set y := p.1.2
  set z := p.2.1
  set w := p.2.2
  unfold a
  apply Finset.card_pos.mpr
  use ((2 * x, 2 * y), (2 * z, 2 * w))
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · have : x^2 + y^2 + z^2 + w^2 = m^2 := h_sum
    nlinarith
  · omega
  · use k + 1
    refine ⟨?_, ?_⟩
    · omega
    · have : (x : ℤ)^2 - (3 * (y : ℤ))^2 = 4^k := hk_eq
      calc
        (2 * (x : ℤ))^2 - (3 * (2 * (y : ℤ)))^2 = 4 * ((x : ℤ)^2 - (3 * (y : ℤ))^2) := by ring
        _ = 4 * 4^k := by rw [this]
        _ = 4^(k + 1) := by ring

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro hn
  by_cases h_even : Even n
  · rcases h_even with ⟨m, rfl⟩
    have hm : m > 0 := by omega
    have h_eq : 2 * m = m + m := by omega
    have h_lt : m < m + m := by omega
    have h_am : a m > 0 := ih m h_lt hm
    have h_even_am : a (2 * m) > 0 := a_even m h_am
    rw [h_eq] at h_even_am
    exact h_even_am
  · rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · exact (h_even (by decide : Even 0)).elim
    · apply a_pos_of_exists 1 1 0 0 0 0 <;> decide
    · exact (h_even (by decide : Even 2)).elim
    · apply a_pos_of_exists 3 1 0 2 2 0 <;> decide
    · exact (h_even (by decide : Even 4)).elim
    · apply a_pos_of_exists 5 4 0 0 3 2 <;> decide
    · exact (h_even (by decide : Even 6)).elim
    · apply a_pos_of_exists 7 2 0 3 6 1 <;> decide
    · exact (h_even (by decide : Even 8)).elim
    · apply a_pos_of_exists 9 1 0 4 8 0 <;> decide
    · exact (h_even (by decide : Even 10)).elim
    · apply a_pos_of_exists 11 2 0 6 9 1 <;> decide
    · exact (h_even (by decide : Even 12)).elim
    · apply a_pos_of_exists 13 4 0 3 12 2 <;> decide
    · exact (h_even (by decide : Even 14)).elim
    · apply a_pos_of_exists 15 2 0 5 14 1 <;> decide
    · exact (h_even (by decide : Even 16)).elim
    · apply a_pos_of_exists 17 1 0 12 12 0 <;> decide
    · exact (h_even (by decide : Even 18)).elim
    · apply a_pos_of_exists 19 1 0 6 18 0 <;> decide
    · exact (h_even (by decide : Even 20)).elim
    · apply a_pos_of_exists 21 4 0 5 20 2 <;> decide
    · exact (h_even (by decide : Even 22)).elim
    · apply a_pos_of_exists 23 10 2 5 20 3 <;> decide
    · exact (h_even (by decide : Even 24)).elim
    · apply a_pos_of_exists 25 10 2 11 20 3 <;> decide
    · exact (h_even (by decide : Even 26)).elim
    · apply a_pos_of_exists 27 2 0 7 26 1 <;> decide
    · exact (h_even (by decide : Even 28)).elim
    · apply a_pos_of_exists 29 16 0 3 24 4 <;> decide
    · exact (h_even (by decide : Even 30)).elim
    · apply a_pos_of_exists 31 10 2 4 29 3 <;> decide
    · exact (h_even (by decide : Even 32)).elim
    · apply a_pos_of_exists 33 1 0 8 32 0 <;> decide
    · exact (h_even (by decide : Even 34)).elim
    · apply a_pos_of_exists 35 1 0 18 30 0 <;> decide
    · exact (h_even (by decide : Even 36)).elim
    · apply a_pos_of_exists 37 8 0 3 36 3 <;> decide
    · exact (h_even (by decide : Even 38)).elim
    · apply a_pos_of_exists 39 2 0 19 34 1 <;> decide
    · exact (h_even (by decide : Even 40)).elim
    · apply a_pos_of_exists 41 4 0 12 39 2 <;> decide
    · exact (h_even (by decide : Even 42)).elim
    · apply a_pos_of_exists 43 2 0 9 42 1 <;> decide
    · exact (h_even (by decide : Even 44)).elim
    · apply a_pos_of_exists 45 4 0 28 35 2 <;> decide
    · exact (h_even (by decide : Even 46)).elim
    · apply a_pos_of_exists 47 2 0 21 42 1 <;> decide
    · exact (h_even (by decide : Even 48)).elim
    · apply a_pos_of_exists 49 4 0 9 48 2 <;> decide
    · exact (h_even (by decide : Even 50)).elim
    · apply a_pos_of_exists 51 1 0 10 50 0 <;> decide
    · exact (h_even (by decide : Even 52)).elim
    · apply a_pos_of_exists 53 8 0 12 51 3 <;> decide
    · exact (h_even (by decide : Even 54)).elim
    · apply a_pos_of_exists 55 20 4 20 47 4 <;> decide
    · exact (h_even (by decide : Even 56)).elim
    · apply a_pos_of_exists 57 4 0 23 52 2 <;> decide
    · exact (h_even (by decide : Even 58)).elim
    · apply a_pos_of_exists 59 20 4 16 53 4 <;> decide
    · exact (h_even (by decide : Even 60)).elim
    · apply a_pos_of_exists 61 10 2 41 44 3 <;> decide
    · exact (h_even (by decide : Even 62)).elim
    · apply a_pos_of_exists 63 2 0 11 62 1 <;> decide
    · exact (h_even (by decide : Even 64)).elim
    · apply a_pos_of_exists 65 10 2 5 64 3 <;> decide
    · exact (h_even (by decide : Even 66)).elim
    · apply a_pos_of_exists 67 10 2 17 64 3 <;> decide
    · exact (h_even (by decide : Even 68)).elim
    · apply a_pos_of_exists 69 4 0 11 68 2 <;> decide
    · exact (h_even (by decide : Even 70)).elim
    · apply a_pos_of_exists 71 10 2 29 64 3 <;> decide
    · exact (h_even (by decide : Even 72)).elim
    · apply a_pos_of_exists 73 1 0 12 72 0 <;> decide
    · exact (h_even (by decide : Even 74)).elim
    · apply a_pos_of_exists 75 10 2 36 65 3 <;> decide
    · exact (h_even (by decide : Even 76)).elim
    · apply a_pos_of_exists 77 4 0 27 72 2 <;> decide
    · exact (h_even (by decide : Even 78)).elim
    · apply a_pos_of_exists 79 10 2 19 76 3 <;> decide
    · exact (h_even (by decide : Even 80)).elim
    · apply a_pos_of_exists 81 1 0 28 76 0 <;> decide
    · exact (h_even (by decide : Even 82)).elim
    · apply a_pos_of_exists 83 2 0 18 81 1 <;> decide
    · exact (h_even (by decide : Even 84)).elim
    · apply a_pos_of_exists 85 4 0 45 72 2 <;> decide
    · exact (h_even (by decide : Even 86)).elim
    · apply a_pos_of_exists 87 2 0 13 86 1 <;> decide
    · exact (h_even (by decide : Even 88)).elim
    · apply a_pos_of_exists 89 8 0 36 81 3 <;> decide
    · exact (h_even (by decide : Even 90)).elim
    · apply a_pos_of_exists 91 10 2 16 89 3 <;> decide
    · exact (h_even (by decide : Even 92)).elim
    · apply a_pos_of_exists 93 4 0 13 92 2 <;> decide
    · exact (h_even (by decide : Even 94)).elim
    · apply a_pos_of_exists 95 20 4 47 80 4 <;> decide
    · exact (h_even (by decide : Even 96)).elim
    · apply a_pos_of_exists 97 10 2 29 92 3 <;> decide
    · exact (h_even (by decide : Even 98)).elim
    · apply a_pos_of_exists 99 1 0 14 98 0 <;> decide
    · exact (h_even (by decide : Even 100)).elim
    · sorry
