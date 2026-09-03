import FormalConjecturesUtil

/-! Balanced-flow constraints on finite-window carry certificates.
These results do not settle Erdős 406. -/
namespace Erdos406WindowCarry
open scoped BigOperators

lemma sum_mod_blocks (a b : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (a * b), f (j % b) =
      (a : ℝ) * ∑ j ∈ Finset.range b, f j := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hh : (∑ j ∈ Finset.range b, f ((a * b + j) % b)) =
        ∑ j ∈ Finset.range b, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [hh]
    push_cast
    ring

lemma sum_div_blocks (a b : ℕ) (ha : 0 < a) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (a * b), f (j / a) =
      (a : ℝ) * ∑ j ∈ Finset.range b, f j := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have hh : (∑ j ∈ Finset.range a, f ((a * b + j) / a)) = (a : ℝ) * f b := by
      calc
        _ = ∑ _j ∈ Finset.range a, f b := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Nat.mul_add_div ha, Nat.div_eq_of_lt (Finset.mem_range.mp hj), Nat.add_zero]
        _ = _ := by simp
    rw [hh]
    ring

/-- In the complete finite-window carry graph, the input and output block
weights have the same total, as do the two endpoint potentials. Consequently
nonnegative transition slack must vanish on every edge. -/
theorem carry_inequalities_are_equalities (B : ℕ) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * B,
      P (j % (4 * B)) ≤ P (j / 3) + f (j % (3 * B)) - f (j / 4)) :
    ∀ j < 12 * B,
      P (j % (4 * B)) = P (j / 3) + f (j % (3 * B)) - f (j / 4) := by
  have hpmod : (∑ j ∈ Finset.range (12 * B), P (j % (4 * B))) =
      3 * ∑ j ∈ Finset.range (4 * B), P j := by
    simpa [← Nat.mul_assoc] using sum_mod_blocks 3 (4 * B) P
  have hpdiv : (∑ j ∈ Finset.range (12 * B), P (j / 3)) =
      3 * ∑ j ∈ Finset.range (4 * B), P j := by
    simpa [← Nat.mul_assoc] using sum_div_blocks 3 (4 * B) (by decide) P
  have hfmod : (∑ j ∈ Finset.range (12 * B), f (j % (3 * B))) =
      4 * ∑ j ∈ Finset.range (3 * B), f j := by
    simpa [← Nat.mul_assoc] using sum_mod_blocks 4 (3 * B) f
  have hfdiv : (∑ j ∈ Finset.range (12 * B), f (j / 4)) =
      4 * ∑ j ∈ Finset.range (3 * B), f j := by
    simpa [← Nat.mul_assoc] using sum_div_blocks 4 (3 * B) (by decide) f
  have he : (∑ j ∈ Finset.range (12 * B), P (j % (4 * B))) =
      ∑ j ∈ Finset.range (12 * B),
        (P (j / 3) + f (j % (3 * B)) - f (j / 4)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hpmod, hpdiv, hfmod, hfdiv]
    ring
  have hh := (Finset.sum_eq_sum_iff_of_le
    (fun j hj => hstep j (Finset.mem_range.mp hj))).mp he
  exact fun j hj => hh j (Finset.mem_range.mpr hj)

/-- With no block memory, the bulk weights are necessarily constant.
No assertion about arbitrary state-dependent automata is made. -/
theorem memory_zero_rigidity (f P : ℕ → ℝ)
    (hstep : ∀ j < 12,
      P (j % 4) ≤ P (j / 3) + f (j % 3) - f (j / 4)) :
    (∀ d < 3, f d = f 0) ∧ (∀ c < 4, P c = P 0) := by
  have he := carry_inequalities_are_equalities 1 f P (by simpa using hstep)
  have h1 := he 1 (by decide)
  have h2 := he 2 (by decide)
  have h3 := he 3 (by decide)
  have h4 := he 4 (by decide)
  have h5 := he 5 (by decide)
  norm_num at h1 h2 h3 h4 h5
  constructor
  · intro d hd
    interval_cases d <;> linarith
  · intro c hc
    interval_cases c <;> linarith

noncomputable def avg3 (f : ℕ → ℝ) (B j : ℕ) : ℝ :=
  (f j + f (j + B) + f (j + 2 * B)) / 3

lemma block_mod (B u k : ℕ) (hB : 0 < B) (hu : u < B) :
    (u + B * k) % (3 * B) = u + B * (k % 3) := by
  rw [Nat.mul_comm 3 B, Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hu, Nat.add_mul_div_left u k hB,
    Nat.div_eq_of_lt hu, zero_add]

lemma rotating_three_blocks (B j : ℕ) (hB : 0 < B) (f : ℕ → ℝ) :
    f (j % (3 * B)) + f ((j + 4 * B) % (3 * B)) +
      f ((j + 8 * B) % (3 * B)) =
    f (j % B) + f (j % B + B) + f (j % B + 2 * B) := by
  let u := j % B
  let t := j / B
  have hu : u < B := Nat.mod_lt _ hB
  have hj : j = u + B * t := (Nat.mod_add_div j B).symm
  have hm : j % B = u := rfl
  rw [hm, hj]
  rw [show u + B * t + 4 * B = u + B * (t + 4) by ring,
    show u + B * t + 8 * B = u + B * (t + 8) by ring,
    block_mod B u t hB hu, block_mod B u (t + 4) hB hu,
    block_mod B u (t + 8) hB hu]
  have ht : t % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [Nat.add_mod t 4 3, Nat.add_mod t 8 3]
  norm_num only at *
  generalize htval : t % 3 = a at *
  interval_cases a <;> norm_num [Nat.mul_comm] <;> ring

lemma average_carry (C : ℕ) (hC : 0 < C) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * (3 * C),
      P (j % (4 * (3 * C))) =
        P (j / 3) + f (j % (3 * (3 * C))) - f (j / 4)) :
    ∀ j < 4 * (3 * C),
      P j = avg3 P (4 * C) (j / 3) +
        avg3 f (3 * C) (j % (3 * C)) - avg3 f (3 * C) (j / 4) := by
  intro j hj
  have h0 := hstep j (by omega)
  have h1 := hstep (j + 4 * (3 * C)) (by omega)
  have h2 := hstep (j + 8 * (3 * C)) (by omega)
  have hout0 : j % (4 * (3 * C)) = j := Nat.mod_eq_of_lt hj
  have hout1 : (j + 4 * (3 * C)) % (4 * (3 * C)) = j := by
    rw [Nat.add_mod_right, hout0]
  have hout2 : (j + 8 * (3 * C)) % (4 * (3 * C)) = j := by
    rw [show 8 * (3 * C) = (4 * (3 * C)) * 2 by ring,
      Nat.add_mul_mod_self_left, hout0]
  have hi13 : (j + 4 * (3 * C)) / 3 = j / 3 + 4 * C := by omega
  have hi23 : (j + 8 * (3 * C)) / 3 = j / 3 + 2 * (4 * C) := by omega
  have hi14 : (j + 4 * (3 * C)) / 4 = j / 4 + 3 * C := by omega
  have hi24 : (j + 8 * (3 * C)) / 4 = j / 4 + 2 * (3 * C) := by omega
  rw [hout0] at h0
  rw [hout1, hi13, hi14] at h1
  rw [hout2, hi23, hi24] at h2
  have hf := rotating_three_blocks (3 * C) j (by omega) f
  dsimp [avg3]
  linarith

lemma residual_carry (C : ℕ) (hC : 0 < C) (f P G Q : ℕ → ℝ)
    (hstep : ∀ j < 12 * (3 * C),
      P (j % (4 * (3 * C))) =
        P (j / 3) + f (j % (3 * (3 * C))) - f (j / 4))
    (hp : ∀ j < 4 * (3 * C),
      P j = Q (j / 3) + G (j % (3 * C)) - G (j / 4)) :
    let F := fun j => f j - G (j % (3 * C)) + G (j / 3)
    ∀ j < 12 * (3 * C),
      Q (j / 3 % (4 * C)) = Q (j / 3 / 3) +
        F (j % (3 * (3 * C))) - F (j / 4) := by
  dsimp only
  intro j hj
  have he := hstep j hj
  rw [hp _ (Nat.mod_lt _ (by omega)), hp _ (by omega)] at he
  have h43 : j % (4 * (3 * C)) / 3 = j / 3 % (4 * C) := by
    rw [show 4 * (3 * C) = 3 * (4 * C) by ring,
      Nat.mod_mul_right_div_self]
  have h44 : j % (4 * (3 * C)) / 4 = j / 4 % (3 * C) :=
    Nat.mod_mul_right_div_self j 4 (3 * C)
  have h33 : j % (3 * (3 * C)) / 3 = j / 3 % (3 * C) :=
    Nat.mod_mul_right_div_self j 3 (3 * C)
  have hm4 : j % (4 * (3 * C)) % (3 * C) = j % (3 * C) :=
    Nat.mod_mod_of_dvd j (dvd_mul_left _ _)
  have hm3 : j % (3 * (3 * C)) % (3 * C) = j % (3 * C) :=
    Nat.mod_mod_of_dvd j (dvd_mul_left _ _)
  have hd : j / 3 / 4 = j / 4 / 3 := by
    simp only [Nat.div_div_eq_div_mul]
  rw [h43, hm4, h44, hd] at he
  rw [h33, hm3]
  linarith

lemma residual_adjacent (N : ℕ) (F Q : ℕ → ℝ)
    (hstep : ∀ j < N,
      Q (j / 3) = F j - F (j / 4)) :
    ∀ j < N, j % 3 ≠ 0 → F j = F (j - 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hmod
    have hjpos : 0 < j := by omega
    have he := hstep j hj
    have he' := hstep (j - 1) (by omega)
    have hd3 : j / 3 = (j - 1) / 3 := by omega
    rw [← hd3] at he'
    have hlow : F (j / 4) = F ((j - 1) / 4) := by
      by_cases h4 : j % 4 = 0
      · have hpos4 : 0 < j / 4 := by omega
        have hl : j / 4 < j := Nat.div_lt_self hjpos (by decide)
        have hm : j / 4 % 3 ≠ 0 := by omega
        have hi := ih (j / 4) hl (by omega) hm
        have hd4 : (j - 1) / 4 = j / 4 - 1 := by omega
        rwa [hd4]
      · have hd4 : j / 4 = (j - 1) / 4 := by omega
        rw [hd4]
    linarith

lemma constant_in_triples (N : ℕ) (F : ℕ → ℝ)
    (hstep : ∀ j < N, j % 3 ≠ 0 → F j = F (j - 1)) :
    ∀ j < N, F j = F (3 * (j / 3)) := by
  intro j hj
  have hm : j % 3 < 3 := Nat.mod_lt _ (by decide)
  by_cases h0 : j % 3 = 0
  · have he : j = 3 * (j / 3) := by omega
    exact congrArg F he
  have he := hstep j hj h0
  by_cases h1 : j % 3 = 1
  · have he' : j - 1 = 3 * (j / 3) := by omega
    rwa [he'] at he
  · have h2 : j % 3 = 2 := by omega
    have he' := hstep (j - 1) (by omega) (by omega)
    have hj2 : j - 1 - 1 = 3 * (j / 3) := by omega
    rw [he, he', hj2]

/-- Exact carry identities on a full ternary window have only common
coboundary solutions. This concerns full-window additive weights, not all
finite automata or arbitrary functions of the integer. -/
theorem full_window_cohomology (r : ℕ) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) = P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4)) :
    ∃ (g : ℕ → ℝ) (μ ν : ℝ),
      (∀ j < 3 * 3 ^ r, f j = μ + g (j % 3 ^ r) - g (j / 3)) ∧
      (∀ j < 4 * 3 ^ r, P j = ν + g (j % 3 ^ r) - g (j / 4)) := by
  induction r generalizing f P with
  | zero =>
    have hh := memory_zero_rigidity f P (fun j hj => le_of_eq (by simpa using hstep j (by simpa using hj)))
    refine ⟨fun _ => 0, f 0, P 0, ?_, ?_⟩
    · simpa using hh.1
    · simpa using hh.2
  | succ r ih =>
    let C := 3 ^ r
    have hC : 0 < C := by dsimp [C]; positivity
    have hpow : 3 ^ (r + 1) = 3 * C := by dsimp [C]; rw [pow_succ]; ring
    rw [hpow] at hstep ⊢
    let G := avg3 f (3 * C)
    let Q := avg3 P (4 * C)
    let F := fun j => f j - G (j % (3 * C)) + G (j / 3)
    let H := fun j => F (3 * j)
    have hp : ∀ j < 4 * (3 * C),
        P j = Q (j / 3) + G (j % (3 * C)) - G (j / 4) :=
      average_carry C hC f P hstep
    have hr : ∀ j < 12 * (3 * C),
        Q (j / 3 % (4 * C)) = Q (j / 3 / 3) +
          F (j % (3 * (3 * C))) - F (j / 4) :=
      residual_carry C hC f P G Q hstep hp
    have hnear : ∀ j < 3 * (3 * C),
        (fun a => Q (a % (4 * C)) - Q (a / 3)) (j / 3) = F j - F (j / 4) := by
      intro j hj
      have hh := hr j (by omega)
      rw [Nat.mod_eq_of_lt hj] at hh
      dsimp only
      linarith
    have hblock : ∀ j < 3 * (3 * C), F j = H (j / 3) :=
      constant_in_triples _ F (residual_adjacent _ F
        (fun a => Q (a % (4 * C)) - Q (a / 3)) hnear)
    have hred : ∀ j < 12 * C,
        Q (j % (4 * C)) = Q (j / 3) + H (j % (3 * C)) - H (j / 4) := by
      intro j hj
      have hh := hr (3 * j) (by omega)
      rw [hblock _ (Nat.mod_lt _ (by omega)), hblock _ (by omega)] at hh
      have he1 : (3 * j) % (3 * (3 * C)) / 3 = j % (3 * C) := by
        rw [Nat.mod_mul_right_div_self]
        simp
      have he2 : (3 * j) / 4 / 3 = j / 4 := by omega
      have he0 : 3 * j / 3 = j := by omega
      simpa only [he0, he1, he2] using hh
    obtain ⟨g, μ, ν, hg, hq⟩ := ih H Q hred
    refine ⟨fun j => G j + g (j / 3), μ, ν, ?_, ?_⟩
    · intro j hj
      have hb := hblock j hj
      have he := hg (j / 3) (by change j / 3 < 3 * C; omega)
      have hm : j % (3 * C) / 3 = j / 3 % C := Nat.mod_mul_right_div_self j 3 C
      dsimp only [F] at hb
      change H (j / 3) = μ + g (j / 3 % C) - g (j / 3 / 3) at he
      dsimp only
      rw [hm]
      linarith
    · intro j hj
      have hb := hp j hj
      have he := hq (j / 3) (by change j / 3 < 4 * C; omega)
      have hm : j % (3 * C) / 3 = j / 3 % C := Nat.mod_mul_right_div_self j 3 C
      have hd : j / 3 / 4 = j / 4 / 3 := by simp only [Nat.div_div_eq_div_mul]
      change Q (j / 3) = ν + g (j / 3 % C) - g (j / 3 / 4) at he
      dsimp only
      rw [hm, ← hd]
      linarith

/-- The inequality version follows from balanced flow. No subcritical
certificate is constructed by this theorem. -/
theorem full_window_inequality_cohomology (r : ℕ) (f P : ℕ → ℝ)
    (hstep : ∀ j < 12 * 3 ^ r,
      P (j % (4 * 3 ^ r)) ≤ P (j / 3) + f (j % (3 * 3 ^ r)) - f (j / 4)) :
    ∃ (g : ℕ → ℝ) (μ ν : ℝ),
      (∀ j < 3 * 3 ^ r, f j = μ + g (j % 3 ^ r) - g (j / 3)) ∧
      (∀ j < 4 * 3 ^ r, P j = ν + g (j % 3 ^ r) - g (j / 4)) :=
  full_window_cohomology r f P (carry_inequalities_are_equalities (3 ^ r) f P hstep)

#print axioms full_window_cohomology
#print axioms full_window_inequality_cohomology
#print axioms residual_carry
#print axioms residual_adjacent
#print axioms average_carry
#print axioms carry_inequalities_are_equalities
#print axioms memory_zero_rigidity
end Erdos406WindowCarry
