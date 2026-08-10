import FormalConjectures.Util.ProblemImports

open Nat Finset Int

noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)
  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;
    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )


lemma a_pos_of_witness {n x y z w k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n)
    (hsum : x^2 + y^2 + z^2 + w^2 = n^2)
    (hzw : z ≤ w)
    (hk : k ≤ n)
    (hpell : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) : a n > 0 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨((x, y), (z, w)), ?_⟩
  simp [hx, hy, hz, hw, hsum, hzw]
  exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, hpell⟩

lemma inspect {N : ℕ} (h : a N > 0) : True := by
  unfold a at h
  have hn := Finset.card_pos.mp h
  rcases hn with ⟨p,hp⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  trivial


lemma scale_a_pos {N r : ℕ} (hN : 0 < N) (h : a N > 0) : a (2^r * N) > 0 := by
  unfold a at h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  rcases p with ⟨⟨x,y⟩,⟨z,w⟩⟩
  rcases hp with ⟨hmem, hsum, hzw, hkex⟩
  rcases hmem with ⟨⟨hxmem, hymem⟩, hzmem, hwmem⟩
  rcases hkex with ⟨k, hkmem, hpell⟩
  have hx : x ≤ N := hxmem
  have hy : y ≤ N := hymem
  have hz : z ≤ N := hzmem
  have hw : w ≤ N := hwmem
  have hk : k ≤ N := hkmem
  let T := 2^r
  have hTpos : 0 < T := by positivity
  refine a_pos_of_witness (n:=T*N) (x:=T*x) (y:=T*y) (z:=T*z) (w:=T*w) (k:=k+r) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Nat.mul_le_mul_left _ hx
  · exact Nat.mul_le_mul_left _ hy
  · exact Nat.mul_le_mul_left _ hz
  · exact Nat.mul_le_mul_left _ hw
  · calc
      (T*x)^2 + (T*y)^2 + (T*z)^2 + (T*w)^2
          = T^2 * (x^2 + y^2 + z^2 + w^2) := by ring
      _ = T^2 * N^2 := by rw [hsum]
      _ = (T*N)^2 := by ring
  · exact Nat.mul_le_mul_left _ hzw
  · have hkN : k + r ≤ N + r := by omega
    have hNr : N + r ≤ N * 2^r := by
      induction r with
      | zero => simp
      | succ r ih =>
          have hN1 : 1 ≤ N := hN
          calc
            N + (r+1) = N + r + 1 := by ring
            _ ≤ N * 2^r + 1 := by omega
            _ ≤ N * 2^r * 2 := by nlinarith [show 1 ≤ N * 2^r by positivity]
            _ = N * 2^(r+1) := by ring
    calc
      k + r ≤ N + r := hkN
      _ ≤ N * 2^r := hNr
      _ = T * N := by dsimp [T]; ring
  · subst T
    rw [pow_add]
    norm_num [Nat.cast_mul, Nat.cast_pow] at hpell ⊢
    rw [← hpell]
    ring
