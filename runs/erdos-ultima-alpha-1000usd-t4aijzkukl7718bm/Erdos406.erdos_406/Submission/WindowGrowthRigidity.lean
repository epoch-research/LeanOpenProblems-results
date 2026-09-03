import Submission.WindowPotentialObstruction

/-! Global affine growth already forces the bulk carry certificate for a
full-window additive recurrence. These are obstructions to a proof strategy,
not a settlement of Erdős 406. -/
namespace Erdos406WindowCarry

lemma uniform_delta_lower_bound (B : ℕ) (hB : 0 < B) (f V : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * B)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1)) :
    ∃ L : ℝ, ∀ n, 0 < n → ∀ c < 4, L ≤ V (4 * n + c) - V n := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun j : Fin (3 * B) => |f j.val|)).bddAbove
  have hbound (j : ℕ) : |f (j % (3 * B))| ≤ M :=
    hM ⟨⟨j % (3 * B), Nat.mod_lt _ (by omega)⟩, rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbound 0)
  have hedge (n c d e cp : ℕ) (hn : 0 < n) (hd : d < 3) (he : e < 3)
      (har : 4 * d + cp = 3 * c + e) :
      V (4 * n + c) - V n ≥
        V (4 * (3 * n + d) + cp) - V (3 * n + d) - 2 * M := by
    have hi := hrec (3 * n + d) (by omega)
    have ho := hrec (3 * (4 * n + c) + e) (by omega)
    have hid : (3 * n + d) / 3 = n := by omega
    have hod : (3 * (4 * n + c) + e) / 3 = 4 * n + c := by omega
    have hv : 4 * (3 * n + d) + cp = 3 * (4 * n + c) + e := by omega
    rw [hid] at hi
    rw [hod] at ho
    have hbi := abs_le.mp (hbound (3 * n + d))
    have hbo := abs_le.mp (hbound (3 * (4 * n + c) + e))
    rw [hv]
    linarith
  have hzero (n : ℕ) (hn : 0 < n) : 1 - 2 * M ≤ V (4 * n) - V n := by
    have hh := hedge n 0 0 1 1 hn (by decide) (by decide) (by decide)
    have hg := hgrow (3 * n)
    simp only [Nat.add_zero] at hh
    linarith
  refine ⟨1 - 4 * M, ?_⟩
  intro n hn c hc
  interval_cases c
  · have hh := hzero n hn
    simp only [Nat.add_zero]
    linarith
  · have hh := hgrow n
    linarith
  · have hh := hedge n 2 2 2 0 hn (by decide) (by decide) (by decide)
    have hz := hzero (3 * n + 2) (by omega)
    simp only [Nat.add_zero] at hh
    linarith
  · have hh := hedge n 3 2 0 1 hn (by decide) (by decide) (by decide)
    have hg := hgrow (3 * n + 2)
    linarith

lemma carry_delta_step (B : ℕ) (_hB : 0 < B) (f V : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * B)))
    (j n : ℕ) (hj : j < 12 * B) (hn : 0 < n)
    (hnmod : n % B = j / 3 / 4) :
    let m := 3 * n + j / 4 % 3
    m % B = j % (4 * B) / 4 ∧
      V (4 * m + j % 4) - V m =
        V (4 * n + j / 3 % 4) - V n + f (j % (3 * B)) - f (j / 4) := by
  dsimp only
  let m := 3 * n + j / 4 % 3
  have hd : j / 4 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hmdiv : m / 3 = n := by dsimp [m]; omega
  have hmdigit : m % 3 = j / 4 % 3 := by dsimp [m]; omega
  have hsmall : j / 4 < 3 * B := by omega
  have himod : m % (3 * B) = j / 4 := by
    rw [Nat.mod_mul, hmdigit, hmdiv, hnmod]
    omega
  have hout : 4 * m + j % 4 = 3 * (4 * n + j / 3 % 4) + j % 3 := by
    dsimp [m]
    omega
  have hodiv : (4 * m + j % 4) / 3 = 4 * n + j / 3 % 4 := by
    rw [hout]
    omega
  have homod : (4 * m + j % 4) % (3 * B) = j % (3 * B) := by
    have he : 4 * (j / 4) + j % 4 = j := by omega
    calc
      _ = (4 * (m % (3 * B)) + j % 4) % (3 * B) := by
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      _ = _ := by rw [himod, he]
  constructor
  · have hh := congrArg (fun a : ℕ => a % B) himod
    dsimp only at hh
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)] at hh
    rw [Nat.mod_mul_right_div_self]
    exact hh
  · have hi := hrec m (by dsimp [m]; omega)
    have ho := hrec (4 * m + j % 4) (by dsimp [m]; omega)
    rw [hmdiv, himod] at hi
    rw [hodiv, homod] at ho
    change V (4 * m + j % 4) - V m = _
    linarith

/-- No finite-state certificate hypothesis is needed: it is obtained by
minimizing actual value differences at each residue/carry state. -/
theorem carry_potential_of_global_growth (B : ℕ) (hB : 0 < B) (f V : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * B)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1)) :
    ∃ P : ℕ → ℝ, ∀ j < 12 * B,
      P (j % (4 * B)) ≤ P (j / 3) + f (j % (3 * B)) - f (j / 4) := by
  obtain ⟨L, hL⟩ := uniform_delta_lower_bound B hB f V hrec hgrow
  let S := fun x : ℕ => {z : ℝ | ∃ n : ℕ, 0 < n ∧ n % B = x / 4 ∧
    z = V (4 * n + x % 4) - V n}
  have hb (x : ℕ) : BddBelow (S x) := by
    refine ⟨L, ?_⟩
    rintro z ⟨n, hn, _hm, rfl⟩
    exact hL n hn (x % 4) (Nat.mod_lt _ (by decide))
  have hne (x : ℕ) (hx : x < 4 * B) : (S x).Nonempty := by
    refine ⟨V (4 * (B + x / 4) + x % 4) - V (B + x / 4), B + x / 4,
      by omega, ?_, rfl⟩
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : x / 4 < B)]
  refine ⟨fun x => sInf (S x), ?_⟩
  intro j hj
  have hx : j / 3 < 4 * B := by omega
  have hy : j % (4 * B) < 4 * B := Nat.mod_lt _ (by omega)
  suffices he : sInf (S (j % (4 * B))) - (f (j % (3 * B)) - f (j / 4)) ≤
      sInf (S (j / 3)) by dsimp only; linarith
  apply le_csInf (hne (j / 3) hx)
  rintro z ⟨n, hn, hnmod, hz⟩
  let m := 3 * n + j / 4 % 3
  have hmpos : 0 < m := by dsimp [m]; omega
  obtain ⟨hm, hdelta⟩ := carry_delta_step B hB f V hrec j n hj hn hnmod
  have hc : j % (4 * B) % 4 = j % 4 :=
    Nat.mod_mod_of_dvd j (dvd_mul_right _ _)
  have hmem : V (4 * m + j % 4) - V m ∈ S (j % (4 * B)) := by
    refine ⟨m, hmpos, hm, ?_⟩
    rw [hc]
  have hi := csInf_le (hb (j % (4 * B))) hmem
  dsimp only [m] at hi
  rw [hdelta] at hi
  linarith

lemma recurrence_coboundary_formula (B : ℕ) (hB : 0 < B)
    (f V g : ℕ → ℝ) (μ : ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * B)))
    (hf : ∀ j < 3 * B, f j = μ + g (j % B) - g (j / 3)) :
    ∀ n, V n = V 0 + μ * (Nat.digits 3 n).length + g (n % B) - g 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    have hn : 0 < n := Nat.pos_of_ne_zero hz
    have hi := ih (n / 3) (Nat.div_lt_self hn (by decide))
    have hl : (Nat.digits 3 n).length = (Nat.digits 3 (n / 3)).length + 1 := by
      rw [Nat.digits_of_two_le_of_pos (by decide) hn]
      rfl
    rw [hrec n hn, hi, hf _ (Nat.mod_lt _ (by omega)),
      Nat.mod_mod_of_dvd _ (dvd_mul_left _ _), Nat.mod_mul_right_div_self, hl]
    push_cast
    ring

/-- Every globally growing additive finite-window recurrence is exactly a
length term plus a bounded endpoint correction. This is not assumed as a
certificate ansatz: it follows from global growth. -/
theorem global_growth_window_formula (r : ℕ) (f V : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * 3 ^ r)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1)) :
    ∃ g : ℕ → ℝ, ∀ n,
      V n = V 0 + f 0 * (Nat.digits 3 n).length + g (n % 3 ^ r) - g 0 := by
  have hB : 0 < 3 ^ r := by positivity
  obtain ⟨P, hP⟩ := carry_potential_of_global_growth (3 ^ r) hB f V hrec hgrow
  obtain ⟨g, μ, _ν, hg, _hp⟩ := full_window_inequality_cohomology r f P hP
  have hμ : f 0 = μ := by simpa using hg 0 (by positivity)
  exact ⟨g, hμ ▸ recurrence_coboundary_formula (3 ^ r) hB f V g μ hrec hg⟩

lemma not_subcritical_of_bounded_correction (V : ℕ → ℝ) (a c C K : ℝ)
    (hc : 0 ≤ c)
    (hcorrection : ∀ n, |V n - a * (Nat.digits 3 n).length| ≤ C)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n ≤ c * (Nat.digits 3 n).length + K) :
    ¬ c * Real.log 4 < Real.log 3 := by
  have ha : a ≤ c := by
    have hlong : ∀ L : ℕ, (a - c) * ((L : ℝ) + 1) ≤ K + C := by
      intro L
      have hd : Nat.digits 3 (3 ^ L) = List.replicate L 0 ++ [1] := by
        have hh := Nat.digits_base_pow_mul (b := 3) (k := L) (m := 1)
          (by decide) (by decide)
        simpa only [Nat.mul_one,
          show Nat.digits 3 1 = [1] from by decide +kernel] using hh
      have hg : Nat.digits 3 (3 ^ L) ⊆ [0, 1] := by
        rw [hd]
        intro d hm
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
        rcases hm with ⟨_, rfl⟩ | rfl <;> simp
      have hu := hgood (3 ^ L) hg
      have hl := (abs_le.mp (hcorrection (3 ^ L))).1
      rw [hd] at hu hl
      simp only [List.length_append, List.length_replicate, List.length_singleton,
        Nat.cast_add, Nat.cast_one] at hu hl
      linarith
    by_contra hn
    have hp : 0 < a - c := by linarith
    obtain ⟨L, hL⟩ := exists_nat_gt ((K + C) / (a - c))
    have hh := (div_lt_iff₀ hp).mp hL
    have hl := hlong L
    nlinarith
  apply affine_global_bound_not_subcritical V c C hc hgrow
  intro n
  have hh := (abs_le.mp (hcorrection n)).2
  have hm := mul_le_mul_of_nonneg_right ha
    (show (0 : ℝ) ≤ (Nat.digits 3 n).length by positivity)
  linarith

/-- A universal obstruction for additive fixed-window potentials: global
affine growth and a good-word-only bound cannot have subcritical slope.
No carry-potential hypothesis is present in this statement. -/
theorem no_subcritical_additive_window (r : ℕ) (f V : ℕ → ℝ) (c K : ℝ)
    (hc : 0 ≤ c)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * 3 ^ r)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n ≤ c * (Nat.digits 3 n).length + K) :
    ¬ c * Real.log 4 < Real.log 3 := by
  obtain ⟨g, hg⟩ := global_growth_window_formula r f V hrec hgrow
  obtain ⟨C, hC⟩ := (Set.finite_range
    (fun j : Fin (3 ^ r) => |V 0 + g j.val - g 0|)).bddAbove
  apply not_subcritical_of_bounded_correction V (f 0) c C K hc ?_ hgrow hgood
  intro n
  have hh : |V 0 + g (n % 3 ^ r) - g 0| ≤ C :=
    hC ⟨⟨n % 3 ^ r, Nat.mod_lt _ (by positivity)⟩, rfl⟩
  rw [hg n]
  convert hh using 1
  congr 1
  ring

#print axioms global_growth_window_formula
#print axioms no_subcritical_additive_window
#print axioms uniform_delta_lower_bound
#print axioms carry_delta_step
#print axioms carry_potential_of_global_growth
end Erdos406WindowCarry
