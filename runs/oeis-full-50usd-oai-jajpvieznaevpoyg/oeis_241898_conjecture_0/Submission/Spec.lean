import FormalConjectures.Util.ProblemImports

open List Nat Finset Classical WithBot

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/--
A241898: $a(n)$ is the largest integer such that $n = a(n)^2 + \dots$ is a decomposition of $n$ into a sum of at most four nondecreasing squares.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let P (k : ℕ) : Prop :=
    k > 0 ∧
    ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = n ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k -- Qualified 'some' to resolve ambiguity

  -- We explicitly provide the DecidablePred instance using classical logic, which is sound
  -- because the existential quantifier is over a finite, bounded search space.
  have dec : DecidablePred P := fun k => Classical.dec (P k)

  -- Filter the range of possible bases k up to $\lfloor\sqrt{n}\rfloor$.
  let S : Finset ℕ := @Finset.filter _ P dec (range (n.sqrt + 1))

  -- Finset.max returns `WithBot ℕ`. We use `rec 0 id` to convert to `ℕ`,
  -- mapping ⊥ (empty set max) to 0 and a successful max to its value.
  (S.max).rec 0 id

lemma no1_nat {k : ℕ} (hk8 : 8 ≤ k) (hk27 : k ≤ 27)
    (hsum : k ^ 2 = 736) : False := by
  have nofin : ¬ ∃ k : Fin 20,
      let kk := k.val + 8
      kk ^ 2 = 736 := by
    decide
  apply nofin
  let kf : Fin 20 := ⟨k - 8, by omega⟩
  refine ⟨kf, ?_⟩
  have hkf : kf.val + 8 = k := by dsimp [kf]; omega
  simpa [hkf] using hsum

lemma no2_nat {k x : ℕ} (hk8 : 8 ≤ k) (hk27 : k ≤ 27)
    (hx8 : 8 ≤ x) (hx27 : x ≤ 27) (hkx : k ≤ x)
    (hsum : k ^ 2 + x ^ 2 = 736) : False := by
  have hk19 : k ≤ 19 := by
    by_contra h
    have hk20 : 20 ≤ k := by omega
    have hx20 : 20 ≤ x := by omega
    nlinarith
  have hx25 : x ≤ 25 := by
    by_contra h
    have hx26 : 26 ≤ x := by omega
    nlinarith
  have nofin : ¬ ∃ k : Fin 12, ∃ x : Fin 18,
      let kk := k.val + 8; let xx := x.val + 8
      kk ≤ xx ∧ kk ^ 2 + xx ^ 2 = 736 := by
    decide
  apply nofin
  let kf : Fin 12 := ⟨k - 8, by omega⟩
  let xf : Fin 18 := ⟨x - 8, by omega⟩
  refine ⟨kf, xf, ?_⟩
  have hkf : kf.val + 8 = k := by dsimp [kf]; omega
  have hxf : xf.val + 8 = x := by dsimp [xf]; omega
  simp [hkf, hxf, hkx, hsum]
lemma no3_nat {k x y : ℕ} (hk8 : 8 ≤ k) (hk27 : k ≤ 27)
    (hx8 : 8 ≤ x) (hx27 : x ≤ 27) (hy8 : 8 ≤ y) (hy27 : y ≤ 27)
    (hkx : k ≤ x) (hxy : x ≤ y)
    (hsum : k ^ 2 + x ^ 2 + y ^ 2 = 736) : False := by
  have hk15 : k ≤ 15 := by
    by_contra h
    have hk16 : 16 ≤ k := by omega
    have hx16 : 16 ≤ x := by omega
    have hy16 : 16 ≤ y := by omega
    nlinarith
  have hx19 : x ≤ 19 := by
    by_contra h
    have hx20 : 20 ≤ x := by omega
    have hy20 : 20 ≤ y := by omega
    nlinarith
  have hy24 : y ≤ 24 := by
    by_contra h
    have hy25 : 25 ≤ y := by omega
    nlinarith
  have nofin : ¬ ∃ k : Fin 8, ∃ x : Fin 12, ∃ y : Fin 17,
      let kk := k.val + 8; let xx := x.val + 8; let yy := y.val + 8
      kk ≤ xx ∧ xx ≤ yy ∧ kk ^ 2 + xx ^ 2 + yy ^ 2 = 736 := by
    decide
  apply nofin
  let kf : Fin 8 := ⟨k - 8, by omega⟩
  let xf : Fin 12 := ⟨x - 8, by omega⟩
  let yf : Fin 17 := ⟨y - 8, by omega⟩
  refine ⟨kf, xf, yf, ?_⟩
  have hkf : kf.val + 8 = k := by dsimp [kf]; omega
  have hxf : xf.val + 8 = x := by dsimp [xf]; omega
  have hyf : yf.val + 8 = y := by dsimp [yf]; omega
  simp [hkf, hxf, hyf, hkx, hxy, hsum]
lemma no4_nat {k x y z : ℕ} (hk8 : 8 ≤ k) (hk27 : k ≤ 27)
    (hx8 : 8 ≤ x) (hx27 : x ≤ 27) (hy8 : 8 ≤ y) (hy27 : y ≤ 27)
    (hz8 : 8 ≤ z) (hz27 : z ≤ 27) (hkx : k ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hsum : k ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 736) : False := by
  have hk13 : k ≤ 13 := by
    by_contra h
    have hk14 : 14 ≤ k := by omega
    have hx14 : 14 ≤ x := by omega
    have hy14 : 14 ≤ y := by omega
    have hz14 : 14 ≤ z := by omega
    nlinarith
  have hx15 : x ≤ 15 := by
    by_contra h
    have hx16 : 16 ≤ x := by omega
    have hy16 : 16 ≤ y := by omega
    have hz16 : 16 ≤ z := by omega
    nlinarith
  have hy18 : y ≤ 18 := by
    by_contra h
    have hy19 : 19 ≤ y := by omega
    have hz19 : 19 ≤ z := by omega
    nlinarith
  have hz23 : z ≤ 23 := by
    by_contra h
    have hz24 : 24 ≤ z := by omega
    nlinarith
  have nofin : ¬ ∃ k : Fin 6, ∃ x : Fin 8, ∃ y : Fin 11, ∃ z : Fin 16,
      let kk := k.val + 8; let xx := x.val + 8; let yy := y.val + 8; let zz := z.val + 8
      kk ≤ xx ∧ xx ≤ yy ∧ yy ≤ zz ∧ kk ^ 2 + xx ^ 2 + yy ^ 2 + zz ^ 2 = 736 := by
    decide
  apply nofin
  let kf : Fin 6 := ⟨k - 8, by omega⟩
  let xf : Fin 8 := ⟨x - 8, by omega⟩
  let yf : Fin 11 := ⟨y - 8, by omega⟩
  let zf : Fin 16 := ⟨z - 8, by omega⟩
  refine ⟨kf, xf, yf, zf, ?_⟩
  have hkf : kf.val + 8 = k := by dsimp [kf]; omega
  have hxf : xf.val + 8 = x := by dsimp [xf]; omega
  have hyf : yf.val + 8 = y := by dsimp [yf]; omega
  have hzf : zf.val + 8 = z := by dsimp [zf]; omega
  simp [hkf, hxf, hyf, hzf, hkx, hxy, hyz, hsum]
lemma no_large_P_736 {k : ℕ} (hklarge : 7 < k) :
    ¬ (k > 0 ∧ ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = 736 ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k) := by
  rintro ⟨hkpos, s, hlen0, hlen4, hsum, hsorted, hhead⟩
  cases s with
  | nil => simp at hlen0
  | cons b1 t =>
    cases t with
    | nil =>
      simp at hhead
      subst b1
      simp at hsum
      have hk8 : 8 ≤ k := by omega
      have hk27 : k ≤ 27 := by
        by_contra h
        have h28 : 28 ≤ k := by omega
        nlinarith [sq_nonneg (k:ℤ)]
      exact no1_nat hk8 hk27 hsum
    | cons b2 t =>
      cases t with
      | nil =>
        simp at hhead
        subst b1
        simp at hsum
        rw [List.sorted_cons] at hsorted
        have hk2 : k ≤ b2 := hsorted.1 b2 (by simp)
        have hk8 : 8 ≤ k := by omega
        have hk27 : k ≤ 27 := by
          by_contra h
          have h28 : 28 ≤ k := by omega
          nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ)]
        have hb28 : 8 ≤ b2 := by omega
        have hb227 : b2 ≤ 27 := by
          by_contra h
          have h28 : 28 ≤ b2 := by omega
          nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ)]
        exact no2_nat hk8 hk27 hb28 hb227 hk2 hsum
      | cons b3 t =>
        cases t with
        | nil =>
          simp at hhead
          subst b1
          simp at hsum
          rw [List.sorted_cons] at hsorted
          have hk2 : k ≤ b2 := hsorted.1 b2 (by simp)
          have ht := hsorted.2
          rw [List.sorted_cons] at ht
          have h23 : b2 ≤ b3 := ht.1 b3 (by simp)
          have hk8 : 8 ≤ k := by omega
          have hk27 : k ≤ 27 := by
            by_contra h
            have h28 : 28 ≤ k := by omega
            nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ)]
          have hb28 : 8 ≤ b2 := by omega
          have hb227 : b2 ≤ 27 := by
            by_contra h
            have h28 : 28 ≤ b2 := by omega
            nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ)]
          have hb38 : 8 ≤ b3 := by omega
          have hb327 : b3 ≤ 27 := by
            by_contra h
            have h28 : 28 ≤ b3 := by omega
            nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ)]
          have hsum' : k ^ 2 + b2 ^ 2 + b3 ^ 2 = 736 := by simpa [Nat.add_assoc] using hsum
          exact no3_nat hk8 hk27 hb28 hb227 hb38 hb327 hk2 h23 hsum'
        | cons b4 t =>
          cases t with
          | nil =>
            simp at hhead
            subst b1
            simp at hsum
            rw [List.sorted_cons] at hsorted
            have hk2 : k ≤ b2 := hsorted.1 b2 (by simp)
            have ht := hsorted.2
            rw [List.sorted_cons] at ht
            have h23 : b2 ≤ b3 := ht.1 b3 (by simp)
            have htt := ht.2
            rw [List.sorted_cons] at htt
            have h34 : b3 ≤ b4 := htt.1 b4 (by simp)
            have hk8 : 8 ≤ k := by omega
            have hk27 : k ≤ 27 := by
              by_contra h
              have h28 : 28 ≤ k := by omega
              nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ), sq_nonneg (b4:ℤ)]
            have hb28 : 8 ≤ b2 := by omega
            have hb227 : b2 ≤ 27 := by
              by_contra h
              have h28 : 28 ≤ b2 := by omega
              nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ), sq_nonneg (b4:ℤ)]
            have hb38 : 8 ≤ b3 := by omega
            have hb327 : b3 ≤ 27 := by
              by_contra h
              have h28 : 28 ≤ b3 := by omega
              nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ), sq_nonneg (b4:ℤ)]
            have hb48 : 8 ≤ b4 := by omega
            have hb427 : b4 ≤ 27 := by
              by_contra h
              have h28 : 28 ≤ b4 := by omega
              nlinarith [sq_nonneg (k:ℤ), sq_nonneg (b2:ℤ), sq_nonneg (b3:ℤ), sq_nonneg (b4:ℤ)]
            have hsum' : k ^ 2 + b2 ^ 2 + b3 ^ 2 + b4 ^ 2 = 736 := by simpa [Nat.add_assoc] using hsum
            exact no4_nat hk8 hk27 hb28 hb227 hb38 hb327 hb48 hb427 hk2 h23 h34 hsum'
          | cons b5 t =>
            simp at hlen4
            omega

lemma a736_le7 : a 736 ≤ 7 := by
  unfold a
  dsimp
  set P : ℕ → Prop := fun k => k > 0 ∧ ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = 736 ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k
  set S : Finset ℕ := @Finset.filter _ P (fun k => Classical.dec (P k)) (range ((736).sqrt + 1))
  have hmax : S.max ≤ (7 : WithBot ℕ) := by
    rw [Finset.max_le_iff]
    intro k hk
    by_cases hle : k ≤ 7
    · exact (WithBot.coe_le_coe).2 hle
    · have hklarge : 7 < k := by omega
      have hkP : P k := by
        have hk' : k ≤ (736).sqrt ∧ P k := by
          simpa [S, P, Finset.mem_filter] using hk
        exact hk'.2
      exact (no_large_P_736 hklarge hkP).elim
  cases hm : S.max with
  | bot =>
    change 0 ≤ 7
    norm_num
  | coe m =>
    have hmleWB : (m : WithBot ℕ) ≤ (↑(7 : ℕ) : WithBot ℕ) := by
      simpa only [hm] using hmax
    have hmle : m ≤ 7 := (WithBot.coe_le_coe).1 hmleWB
    change m ≤ 7
    exact hmle

theorem oeis_241898_conjecture_0.disproof : ¬ (∀ n : ℕ, 599 < n → a n > 7) := by
  intro h
  have h736 : a 736 > 7 := h 736 (by norm_num)
  have hle : a 736 ≤ 7 := a736_le7
  omega
