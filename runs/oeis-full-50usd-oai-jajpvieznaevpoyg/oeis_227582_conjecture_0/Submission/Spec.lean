import FormalConjectures.Util.ProblemImports

open BigOperators LinearRecurrence Filter Finset Set
open scoped Topology
set_option compiler.extract_closed false
set_option linter.all false




/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.
-/
def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_0$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0

private def qz (n : ℕ) : ℤ := ((n / 5 : ℕ) : ℤ)
private def bcf (n : ℕ) : ℤ :=
  let q := qz n
  match n % 5 with
  | 0 => 30*q*q + 18*q + 2
  | 1 => 30*q*q + 30*q + 7
  | 2 => 30*q*q + 42*q + 14
  | 3 => 30*q*q + 54*q + 23
  | _ => 30*q*q + 66*q + 35

private def Kseq (n:ℕ):ℕ := (6*n*(n+1)-1)/5

private lemma rec_aux (q r : ℕ) (hr : r < 5) :
    bcf (5*q+r+7) = bcf (5*q+r) - 2*bcf (5*q+r+1) + bcf (5*q+r+2) - bcf (5*q+r+5) + 2*bcf (5*q+r+6) := by
  interval_cases r
  all_goals
    simp only [bcf, qz]
    repeat first | rw [show (5*q+0+7)%5 = 2 by omega] | rw [show (5*q+0)%5 = 0 by omega] | rw [show (5*q+0+1)%5 = 1 by omega] | rw [show (5*q+0+2)%5 = 2 by omega] | rw [show (5*q+0+5)%5 = 0 by omega] | rw [show (5*q+0+6)%5 = 1 by omega]
                 | rw [show (5*q+1+7)%5 = 3 by omega] | rw [show (5*q+1)%5 = 1 by omega] | rw [show (5*q+1+1)%5 = 2 by omega] | rw [show (5*q+1+2)%5 = 3 by omega] | rw [show (5*q+1+5)%5 = 1 by omega] | rw [show (5*q+1+6)%5 = 2 by omega]
                 | rw [show (5*q+2+7)%5 = 4 by omega] | rw [show (5*q+2)%5 = 2 by omega] | rw [show (5*q+2+1)%5 = 3 by omega] | rw [show (5*q+2+2)%5 = 4 by omega] | rw [show (5*q+2+5)%5 = 2 by omega] | rw [show (5*q+2+6)%5 = 3 by omega]
                 | rw [show (5*q+3+7)%5 = 0 by omega] | rw [show (5*q+3)%5 = 3 by omega] | rw [show (5*q+3+1)%5 = 4 by omega] | rw [show (5*q+3+2)%5 = 0 by omega] | rw [show (5*q+3+5)%5 = 3 by omega] | rw [show (5*q+3+6)%5 = 4 by omega]
                 | rw [show (5*q+4+7)%5 = 1 by omega] | rw [show (5*q+4)%5 = 4 by omega] | rw [show (5*q+4+1)%5 = 0 by omega] | rw [show (5*q+4+2)%5 = 1 by omega] | rw [show (5*q+4+5)%5 = 4 by omega] | rw [show (5*q+4+6)%5 = 0 by omega]
    repeat first | rw [show (5*q+0+7)/5 = q+1 by omega] | rw [show (5*q+0)/5 = q by omega] | rw [show (5*q+0+1)/5 = q by omega] | rw [show (5*q+0+2)/5 = q by omega] | rw [show (5*q+0+5)/5 = q+1 by omega] | rw [show (5*q+0+6)/5 = q+1 by omega]
                 | rw [show (5*q+1+7)/5 = q+1 by omega] | rw [show (5*q+1)/5 = q by omega] | rw [show (5*q+1+1)/5 = q by omega] | rw [show (5*q+1+2)/5 = q by omega] | rw [show (5*q+1+5)/5 = q+1 by omega] | rw [show (5*q+1+6)/5 = q+1 by omega]
                 | rw [show (5*q+2+7)/5 = q+1 by omega] | rw [show (5*q+2)/5 = q by omega] | rw [show (5*q+2+1)/5 = q by omega] | rw [show (5*q+2+2)/5 = q by omega] | rw [show (5*q+2+5)/5 = q+1 by omega] | rw [show (5*q+2+6)/5 = q+1 by omega]
                 | rw [show (5*q+3+7)/5 = q+2 by omega] | rw [show (5*q+3)/5 = q by omega] | rw [show (5*q+3+1)/5 = q by omega] | rw [show (5*q+3+2)/5 = q+1 by omega] | rw [show (5*q+3+5)/5 = q+1 by omega] | rw [show (5*q+3+6)/5 = q+1 by omega]
                 | rw [show (5*q+4+7)/5 = q+2 by omega] | rw [show (5*q+4)/5 = q by omega] | rw [show (5*q+4+1)/5 = q+1 by omega] | rw [show (5*q+4+2)/5 = q+1 by omega] | rw [show (5*q+4+5)/5 = q+1 by omega] | rw [show (5*q+4+6)/5 = q+2 by omega]
    norm_num; ring_nf

private lemma bcf_eq_base (n : ℕ) : A227582_base n = bcf n := by
  unfold A227582_base
  let E : LinearRecurrence ℤ := { order := 7, coeffs := ![1, -2, 1, 0, 0, -1, 2] }
  let init : Fin E.order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  change E.mkSol init n = bcf n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [LinearRecurrence.mkSol]
    split_ifs with hlt
    · interval_cases n <;> norm_num [bcf, qz, E, init]
    · have hge : 7 ≤ n := by simpa [E] using le_of_not_gt hlt
      have hrec : bcf n = bcf (n-7) - 2*bcf (n-7+1) + bcf (n-7+2) - bcf (n-7+5) + 2*bcf (n-7+6) := by
        have hm : n - 7 + 7 = n := by omega
        rw [← hm]
        have hr := rec_aux ((n-7)/5) ((n-7)%5) (Nat.mod_lt _ (by norm_num : 0 < 5))
        have hdecomp : n - 7 = 5*((n-7)/5)+(n-7)%5 := by omega
        rw [hdecomp]
        simpa [add_assoc] using hr
      rw [hrec]
      simp [E, Fin.sum_univ_succ]
      rw [ih (n-7) (by omega), ih (n-7+1) (by omega), ih (n-7+2) (by omega),
        ih (n-7+5) (by omega), ih (n-7+6) (by omega)]
      ring_nf

private lemma div_poly0 (q:ℕ): (6*(5*q+1)*(5*q+2)-1)/5 = 30*q*q+18*q+2 := by
  apply Nat.div_eq_of_lt_le <;> ring_nf <;> omega
private lemma div_poly1 (q:ℕ): (6*(5*q+2)*(5*q+3)-1)/5 = 30*q*q+30*q+7 := by
  apply Nat.div_eq_of_lt_le <;> ring_nf <;> omega
private lemma div_poly2 (q:ℕ): (6*(5*q+3)*(5*q+4)-1)/5 = 30*q*q+42*q+14 := by
  apply Nat.div_eq_of_lt_le <;> ring_nf <;> omega
private lemma div_poly3 (q:ℕ): (6*(5*q+4)*(5*q+5)-1)/5 = 30*q*q+54*q+23 := by
  apply Nat.div_eq_of_lt_le <;> ring_nf <;> omega
private lemma div_poly4 (q:ℕ): (6*(5*q+5)*(5*q+6)-1)/5 = 30*q*q+66*q+35 := by
  apply Nat.div_eq_of_lt_le <;> ring_nf <;> omega

private lemma bcf_eq_K (m:ℕ) : bcf m = (Kseq (m+1) : ℤ) := by
  set q := m/5
  have hm : m=5*q+m%5 := by omega
  have hr:= Nat.mod_lt m (by norm_num:0<5)
  interval_cases h : m%5
  all_goals rw [hm]
  · simp [bcf,qz,Kseq, div_poly0]
  · simp [bcf,qz,Kseq, div_poly1]
    rw [show ((5:ℤ)*(q:ℤ)+1)/5=(q:ℤ) by omega]
  · simp [bcf,qz,Kseq, div_poly2]
    rw [show ((5:ℤ)*(q:ℤ)+2)/5=(q:ℤ) by omega]
  · simp [bcf,qz,Kseq, div_poly3]
    rw [show ((5:ℤ)*(q:ℤ)+3)/5=(q:ℤ) by omega]
  · simp [bcf,qz,Kseq, div_poly4]
    rw [show ((5:ℤ)*(q:ℤ)+4)/5=(q:ℤ) by omega]


private lemma deriv_alt5 (x : ℝ) (hxne : 1 + x ≠ 0) :

    HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3 - x^4/4 + x^5/5 - Real.log (1+x))
      (x^5/(1+x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun x : ℝ => x^2/2) (x) x := by convert ((h1.pow 2).div_const (2:ℝ)) using 1 <;> ring_nf
  have h3 : HasDerivAt (fun x : ℝ => x^3/3) (x^2) x := by convert ((h1.pow 3).div_const (3:ℝ)) using 1 <;> ring_nf
  have h4 : HasDerivAt (fun x : ℝ => x^4/4) (x^3) x := by convert ((h1.pow 4).div_const (4:ℝ)) using 1 <;> ring_nf
  have h5 : HasDerivAt (fun x : ℝ => x^5/5) (x^4) x := by convert ((h1.pow 5).div_const (5:ℝ)) using 1 <;> ring_nf
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1+x)) ((1+x)⁻¹) x := by
    have hadd : HasDerivAt (fun x : ℝ => 1+x) 1 x := by convert (hasDerivAt_const x (1:ℝ)).add h1 using 1 <;> ring_nf
    convert hadd.log hxne using 1 <;> ring_nf
  convert ((((h1.sub h2).add h3).sub h4).add h5).sub hlog using 1
  field_simp [hxne]
  ring_nf

private lemma deriv_alt4 (x : ℝ) (hxne : 1 + x ≠ 0) :
    HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3 - x^4/4 - Real.log (1+x))
      (-(x^4)/(1+x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun x : ℝ => x^2/2) (x) x := by convert ((h1.pow 2).div_const (2:ℝ)) using 1 <;> ring_nf
  have h3 : HasDerivAt (fun x : ℝ => x^3/3) (x^2) x := by convert ((h1.pow 3).div_const (3:ℝ)) using 1 <;> ring_nf
  have h4 : HasDerivAt (fun x : ℝ => x^4/4) (x^3) x := by convert ((h1.pow 4).div_const (4:ℝ)) using 1 <;> ring_nf
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1+x)) ((1+x)⁻¹) x := by
    have hadd : HasDerivAt (fun x : ℝ => 1+x) 1 x := by convert (hasDerivAt_const x (1:ℝ)).add h1 using 1 <;> ring_nf
    convert hadd.log hxne using 1 <;> ring_nf
  convert (((h1.sub h2).add h3).sub h4).sub hlog using 1
  field_simp [hxne]
  ring_nf

private lemma log_one_add_le_alt5 {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1+u) ≤ u - u^2/2 + u^3/3 - u^4/4 + u^5/5 := by
  let f : ℝ → ℝ := fun x => x - x^2/2 + x^3/3 - x^4/4 + x^5/5 - Real.log (1+x)
  have hder : ∀ x ∈ Icc 0 u, HasDerivAt f (x^5/(1+x)) x := by
    intro x hx; exact deriv_alt5 x (by linarith [hx.1])
  have hmono : MonotoneOn f (Icc 0 u) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
      (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hder x (interior_subset hx)).hasDerivWithinAt) ?_
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hden : 0 < 1 + x := by linarith [hx.1]
    exact div_nonneg (pow_nonneg hx.1.le 5) hden.le
  have hle := hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
  dsimp [f] at hle
  norm_num at hle
  linarith

private lemma alt4_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    u - u^2/2 + u^3/3 - u^4/4 ≤ Real.log (1+u) := by
  let f : ℝ → ℝ := fun x => x - x^2/2 + x^3/3 - x^4/4 - Real.log (1+x)
  have hder : ∀ x ∈ Icc 0 u, HasDerivAt f (-(x^4)/(1+x)) x := by
    intro x hx; exact deriv_alt4 x (by linarith [hx.1])
  have hanti : AntitoneOn f (Icc 0 u) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 u)
      (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hder x (interior_subset hx)).hasDerivWithinAt) ?_
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hden : 0 < 1 + x := by linarith [hx.1]
    have hfrac : 0 ≤ x ^ 4 / (1 + x) := div_nonneg (pow_nonneg hx.1.le 4) hden.le
    convert neg_nonpos.mpr hfrac using 1; ring_nf
  have hle := hanti ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
  dsimp [f] at hle
  norm_num at hle
  linarith
private noncomputable def F3 (x : ℝ) : ℝ := 1/(2*x)-1/(12*x^2)+1/(120*x^4)
private lemma upper3_step (n : ℕ) (hn : 0 < n) :
    Real.log (((n+1:ℕ):ℝ)/n) - 1/((n+1:ℕ):ℝ) ≤ F3 n - F3 (n+1) := by
  let x : ℝ := 1 / (2 * (n:ℝ) + 1)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    field_simp [show 2 * (n:ℝ) + 1 ≠ 0 by positivity]
    linarith
  have hlog := Real.log_div_le_sum_range_add (x:=x) hx0 hx1 3
  have hratio : (1 + x) / (1 - x) = (((n+1:ℕ):ℝ)/n) := by
    dsimp [x]
    field_simp [show (n:ℝ) ≠ 0 by positivity]
    norm_num; ring_nf
  rw [hratio] at hlog
  have hden : 1 - (1 / (2 * (n:ℝ) + 1)) ^ 2 ≠ 0 := by
    apply ne_of_gt
    refine sub_pos.mpr (pow_lt_one₀ (by positivity : 0 ≤ (1 / (2 * (n:ℝ) + 1) : ℝ)) ?_ (by norm_num : (2:ℕ) ≠ 0))
    dsimp
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    field_simp [show 2 * (n:ℝ) + 1 ≠ 0 by positivity]
    linarith
  have hS : 2 * ((∑ i ∈ range 3, x ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) + x ^ (2 * 3 + 1) / (1 - x ^ 2))
      - 1/((n+1:ℕ):ℝ) ≤ F3 n - F3 (n+1) := by
    dsimp [F3, x]
    norm_num [Finset.sum_range_succ]
    field_simp [show (n:ℝ) ≠ 0 by positivity, show ((n:ℝ)+1) ≠ 0 by positivity,
      show 2 * (n:ℝ) + 1 ≠ 0 by positivity, hden,
      show (n:ℝ) * 4 + (n:ℝ)^2 * 4 ≠ 0 by positivity]
    ring_nf
    field_simp [show (n:ℝ) * 4 + (n:ℝ)^2 * 4 ≠ 0 by positivity]
    rw [← sub_nonneg]
    ring_nf
    positivity
  nlinarith [hlog, hS]

private noncomputable def F0 (x : ℝ) : ℝ :=
  1 / (2*x) - 1/(12*x^2) + 1/(120*x^4) - 1/(252*x^6)

private lemma lower_step (n : ℕ) (hn : 0 < n) :
    F0 n - F0 (n+1) ≤ Real.log (((n+1:ℕ):ℝ)/n) - 1/((n+1:ℕ):ℝ) := by
  let x : ℝ := 1 / (2 * (n:ℝ) + 1)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    field_simp [show 2 * (n:ℝ) + 1 ≠ 0 by positivity]
    linarith
  have hlog := Real.sum_range_le_log_div (x:=x) hx0 hx1 4
  have hratio : (1 + x) / (1 - x) = (((n+1:ℕ):ℝ)/n) := by
    dsimp [x]
    field_simp [show (n:ℝ) ≠ 0 by positivity]
    norm_num
    ring_nf
  rw [hratio] at hlog
  have hS : F0 n - F0 (n+1) + 1/((n+1:ℕ):ℝ) ≤
      2 * (∑ i ∈ range 4, x ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) := by
    dsimp [F0, x]
    norm_num [Finset.sum_range_succ]
    field_simp [show (n:ℝ) ≠ 0 by positivity, show ((n:ℝ)+1) ≠ 0 by positivity,
      show 2 * (n:ℝ) + 1 ≠ 0 by positivity]
    rw [← sub_nonneg]
    ring_nf
    positivity
  nlinarith [hlog, hS]

private lemma tendsto_F0_shift_zero : Tendsto (fun k : ℕ => F0 (((k+1:ℕ):ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (1/2 : ℝ) / (((k+1:ℕ):ℝ))^1) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (1/2 : ℝ) 1 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h2 : Tendsto (fun k : ℕ => (-1/12 : ℝ) / (((k+1:ℕ):ℝ))^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (-1/12 : ℝ) 2 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h4 : Tendsto (fun k : ℕ => (1/120 : ℝ) / (((k+1:ℕ):ℝ))^4) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (1/120 : ℝ) 4 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h6 : Tendsto (fun k : ℕ => (-1/252 : ℝ) / (((k+1:ℕ):ℝ))^6) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (-1/252 : ℝ) 6 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  convert ((h1.add h2).add h4).add h6 using 1
  · ext k; dsimp [F0]; ring_nf
  · norm_num


private lemma remainder_lower (n : ℕ) (hn : 0 < n) :
    F0 n ≤ (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant := by
  let G : ℕ → ℝ := fun k => (harmonic (k+1) : ℝ) - Real.log (k+1) - F0 (((k+1:ℕ):ℝ))
  have hanti : Antitone G := by
    apply antitone_nat_of_succ_le
    intro k
    dsimp [G]
    have hk : 0 < k + 1 := by omega
    have hs := lower_step (k+1) hk
    rw [Real.log_div] at hs
    · have hs' : F0 ((k:ℝ)+1) - F0 ((k:ℝ)+2) ≤
          Real.log ((k:ℝ)+2) - Real.log ((k:ℝ)+1) - 1 / ((k:ℝ)+2) := by
        convert hs using 1 <;> norm_num <;> ring_nf
      rw [harmonic_succ (k+1)]
      push_cast
      ring_nf at hs' ⊢
      linarith [hs']
    · exact ne_of_gt (by positivity : (0:ℝ) < (k+1+1:ℕ))
    · exact ne_of_gt (by positivity : (0:ℝ) < (k+1:ℕ))
  have ht : Tendsto G atTop (𝓝 Real.eulerMascheroniConstant) := by
    dsimp [G]
    have h1 := (Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1))
    have h2 : Tendsto (fun k : ℕ => ((harmonic (k+1) : ℝ) - Real.log (k+1))) atTop (𝓝 Real.eulerMascheroniConstant) := by
      refine h1.congr' (Eventually.of_forall ?_)
      intro k
      simp [Real.eulerMascheroniSeq']
    simpa using h2.sub tendsto_F0_shift_zero
  have hle := hanti.le_of_tendsto ht (n-1)
  have hn' : n - 1 + 1 = n := by omega
  dsimp [G] at hle
  rw [hn'] at hle
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [show (1:ℝ) = ((1:ℕ):ℝ) by norm_num, ← Nat.cast_add]
    exact_mod_cast hn' 
  rw [hcast] at hle
  linarith [hle]


private noncomputable def Uu (n : ℕ) : ℝ := ((n:ℝ)-1)/(n:ℝ)^2
private noncomputable def logU (n : ℕ) : ℝ := ∑ i ∈ Finset.range 5, (-1:ℝ)^i * (Uu n)^(i+1)/(i+1:ℝ)
private noncomputable def logL (n : ℕ) : ℝ := ∑ i ∈ Finset.range 4, (-1:ℝ)^i * (Uu n)^(i+1)/(i+1:ℝ)
private noncomputable def NN (n : ℕ) : ℝ := (n:ℝ)*(n:ℝ)+(n:ℝ)-1
private noncomputable def LD (n : ℕ) : ℝ := -logU n + 2*F0 (n:ℝ) - F3 (NN n)
private noncomputable def UD (n : ℕ) : ℝ := -logL n + 2*F3 (n:ℝ) - F0 (NN n)
private lemma low_pos (m:ℕ): 0 < LD (m+1) - 5/(6*((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)) := by
  dsimp [LD, logU, Uu, F0, F3, NN]
  norm_num [Finset.sum_range_succ]
  have hm1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hm2 : (m:ℝ)+2 ≠ 0 := by positivity
  have hq : (m:ℝ)^2 + 3*(m:ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm1, hm2, hq]
  ring_nf
  field_simp [show (1 + (m:ℝ)*12 + (m:ℝ)^2*58 + (m:ℝ)^3*144 + (m:ℝ)^4*195 + (m:ℝ)^5*144 + (m:ℝ)^6*58 + (m:ℝ)^7*12 + (m:ℝ)^8) ≠ 0 by positivity]
  rw [← sub_pos]
  ring_nf
  positivity

private lemma up_pos (m:ℕ): 0 < 5/(6*((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)-1) - UD (m+1) := by
  dsimp [UD, logL, Uu, F0, F3, NN]
  norm_num [Finset.sum_range_succ]
  have hm1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hq : (m:ℝ)^2 + 3*(m:ℝ) + 1 ≠ 0 := by positivity
  have hr : 6*(m:ℝ)^2 + 18*(m:ℝ) + 11 ≠ 0 := by positivity
  field_simp [hm1, hq, hr]
  ring_nf
  field_simp [show (1 + (m:ℝ)*18 + (m:ℝ)^2*141 + (m:ℝ)^3*630 + (m:ℝ)^4*1770 + (m:ℝ)^5*3258 + (m:ℝ)^6*3989 + (m:ℝ)^7*3258 + (m:ℝ)^8*1770 + (m:ℝ)^9*630 + (m:ℝ)^10*141 + (m:ℝ)^11*18 + (m:ℝ)^12) ≠ 0 by positivity]
  rw [← sub_pos]
  ring_nf
  positivity

private lemma tendsto_F3_shift_zero : Tendsto (fun k : ℕ => F3 (((k+1:ℕ):ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (1/2 : ℝ) / (((k+1:ℕ):ℝ))^1) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (1/2 : ℝ) 1 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h2 : Tendsto (fun k : ℕ => (-1/12 : ℝ) / (((k+1:ℕ):ℝ))^2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (-1/12 : ℝ) 2 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  have h4 : Tendsto (fun k : ℕ => (1/120 : ℝ) / (((k+1:ℕ):ℝ))^4) atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using
      ((tendsto_const_div_pow (1/120 : ℝ) 4 (by norm_num)).comp (tendsto_add_atTop_nat 1))
  convert (h1.add h2).add h4 using 1
  · ext k; dsimp [F3]; ring_nf
  · norm_num

private lemma remainder_upper3 (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant ≤ F3 n := by
  let G : ℕ → ℝ := fun k => (harmonic (k+1) : ℝ) - Real.log (k+1) - F3 (((k+1:ℕ):ℝ))
  have hmono : Monotone G := by
    apply monotone_nat_of_le_succ
    intro k
    dsimp [G]
    have hk : 0 < k + 1 := by omega
    have hs := upper3_step (k+1) hk
    rw [Real.log_div] at hs
    · have hs' : Real.log ((k:ℝ)+2) - Real.log ((k:ℝ)+1) - 1 / ((k:ℝ)+2) ≤
          F3 ((k:ℝ)+1) - F3 ((k:ℝ)+2) := by
        convert hs using 1 <;> norm_num <;> ring_nf
      rw [harmonic_succ (k+1)]
      push_cast
      ring_nf at hs' ⊢
      linarith [hs']
    · exact ne_of_gt (by positivity : (0:ℝ) < (k+1+1:ℕ))
    · exact ne_of_gt (by positivity : (0:ℝ) < (k+1:ℕ))
  have ht : Tendsto G atTop (𝓝 Real.eulerMascheroniConstant) := by
    dsimp [G]
    have h1 := (Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1))
    have h2 : Tendsto (fun k : ℕ => ((harmonic (k+1) : ℝ) - Real.log (k+1))) atTop (𝓝 Real.eulerMascheroniConstant) := by
      refine h1.congr' (Eventually.of_forall ?_)
      intro k
      simp [Real.eulerMascheroniSeq']
    simpa using h2.sub tendsto_F3_shift_zero
  have hle := hmono.ge_of_tendsto ht (n-1)
  have hn' : n - 1 + 1 = n := by omega
  dsimp [G] at hle
  rw [hn'] at hle
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [show (1:ℝ) = ((1:ℕ):ℝ) by norm_num, ← Nat.cast_add]
    exact_mod_cast hn'
  rw [hcast] at hle
  linarith [hle]

private lemma logU_bound (n : ℕ) (hn : 0 < n) : Real.log (1 + Uu n) ≤ logU n := by
  have hu : 0 ≤ Uu n := by
    dsimp [Uu]
    apply div_nonneg
    · have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    · positivity
  have h := log_one_add_le_alt5 (u := Uu n) hu
  dsimp [logU]
  norm_num [Finset.sum_range_succ]
  linarith [h]

private lemma logL_bound (n : ℕ) (hn : 0 < n) : logL n ≤ Real.log (1 + Uu n) := by
  have hu : 0 ≤ Uu n := by
    dsimp [Uu]
    apply div_nonneg
    · have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    · positivity
  have h := alt4_le_log_one_add (u := Uu n) hu
  dsimp [logL]
  norm_num [Finset.sum_range_succ]
  linarith [h]

private lemma one_add_Uu_eq (n : ℕ) (hn : 0 < n) :
    1 + Uu n = NN n / (n:ℝ)^2 := by
  dsimp [Uu, NN]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp [hn0]
  ring_nf

private lemma NN_pos (n : ℕ) (hn : 0 < n) : 0 < NN n := by
  dsimp [NN]
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < (n:ℝ) * (n:ℝ) := by positivity
  nlinarith

private lemma NN_eq_nat (n : ℕ) (hn : 0 < n) : NN n = ((n*n+n-1 : ℕ) : ℝ) := by
  dsimp [NN]
  have hle : 1 ≤ n * n + n := by
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  rw [Nat.cast_sub hle]
  push_cast
  ring_nf

private lemma log_NN_sub_two_log (n : ℕ) (hn : 0 < n) :
    Real.log (1 + Uu n) = Real.log (NN n) - 2 * Real.log (n:ℝ) := by
  rw [one_add_Uu_eq n hn]
  rw [Real.log_div]
  · rw [Real.log_pow]
    ring_nf
  · exact ne_of_gt (NN_pos n hn)
  · positivity

private lemma denom_lower_bound (n : ℕ) (hn : 0 < n) :
    LD n ≤ 2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n*n+n-1)) : ℝ) - Real.eulerMascheroniConstant := by
  let N := n*n+n-1
  have hNpos : 0 < N := by
    dsimp [N]
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  have hRn := remainder_lower n hn
  have hRN0 := remainder_upper3 N hNpos
  have hlog := logU_bound n hn
  have hlogid0 := log_NN_sub_two_log n hn
  have hNN : NN n = (N:ℝ) := by
    dsimp [N]
    exact NN_eq_nat n hn
  have hRN : (harmonic N : ℝ) - Real.log (NN n) - Real.eulerMascheroniConstant ≤ F3 (NN n) := by
    simpa [hNN] using hRN0
  have hlogid : Real.log (1 + Uu n) = Real.log (N:ℝ) - 2 * Real.log (n:ℝ) := by
    simpa [hNN] using hlogid0
  dsimp [LD]
  calc
    -logU n + 2 * F0 (n:ℝ) - F3 (NN n)
        ≤ -Real.log (1 + Uu n) + 2 * ((harmonic n : ℝ) - Real.log (n:ℝ) - Real.eulerMascheroniConstant) - ((harmonic N : ℝ) - Real.log (NN n) - Real.eulerMascheroniConstant) := by
          nlinarith [hRn, hRN, hlog]
    _ = 2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n*n+n-1)) : ℝ) - Real.eulerMascheroniConstant := by
          rw [hNN]
          dsimp [N]
          nlinarith [hlogid]

private lemma denom_upper_bound (n : ℕ) (hn : 0 < n) :
    2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n*n+n-1)) : ℝ) - Real.eulerMascheroniConstant ≤ UD n := by
  let N := n*n+n-1
  have hNpos : 0 < N := by
    dsimp [N]
    have hp : 0 < n * n := Nat.mul_pos hn hn
    omega
  have hRn := remainder_upper3 n hn
  have hRN0 := remainder_lower N hNpos
  have hlog := logL_bound n hn
  have hlogid0 := log_NN_sub_two_log n hn
  have hNN : NN n = (N:ℝ) := by
    dsimp [N]
    exact NN_eq_nat n hn
  have hRN : F0 (NN n) ≤ (harmonic N : ℝ) - Real.log (NN n) - Real.eulerMascheroniConstant := by
    simpa [hNN] using hRN0
  have hlogid : Real.log (1 + Uu n) = Real.log (N:ℝ) - 2 * Real.log (n:ℝ) := by
    simpa [hNN] using hlogid0
  dsimp [UD]
  calc
    2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n*n+n-1)) : ℝ) - Real.eulerMascheroniConstant
      = -Real.log (1 + Uu n) + 2 * ((harmonic n : ℝ) - Real.log (n:ℝ) - Real.eulerMascheroniConstant) - ((harmonic N : ℝ) - Real.log (NN n) - Real.eulerMascheroniConstant) := by
          rw [hNN]
          dsimp [N]
          nlinarith [hlogid]
    _ ≤ -logL n + 2 * F3 (n:ℝ) - F0 (NN n) := by
          nlinarith [hRn, hRN, hlog]

private noncomputable def Den (n : ℕ) : ℝ :=
  2 * (↑(harmonic n) : ℝ) - (↑(harmonic (n*n+n-1)) : ℝ) - Real.eulerMascheroniConstant

private lemma denom_gt_lower_rat (n : ℕ) (hn : 0 < n) :
    5 / (6 * (n:ℝ) * ((n:ℝ)+1)) < Den n := by
  have hlow := low_pos (n-1)
  have hn' : n - 1 + 1 = n := by omega
  have hlow' : 5 / (6 * (n:ℝ) * ((n:ℝ)+1)) < LD n := by
    rw [hn'] at hlow
    nlinarith [hlow]
  have hD := denom_lower_bound n hn
  dsimp [Den]
  nlinarith [hlow', hD]

private lemma denom_lt_upper_rat (n : ℕ) (hn : 0 < n) :
    Den n < 5 / (6 * (n:ℝ) * ((n:ℝ)+1) - 1) := by
  have hup := up_pos (n-1)
  have hn' : n - 1 + 1 = n := by omega
  have hup' : UD n < 5 / (6 * (n:ℝ) * ((n:ℝ)+1) - 1) := by
    rw [hn'] at hup
    nlinarith [hup]
  have hD := denom_upper_bound n hn
  dsimp [Den]
  nlinarith [hup', hD]

private lemma Kseq_le_A_div (n : ℕ) (hn : 0 < n) :
    (Kseq n : ℝ) ≤ ((6*n*(n+1)-1 : ℕ) : ℝ) / 5 := by
  let A : ℕ := 6*n*(n+1)-1
  have hmul : Kseq n * 5 ≤ A := by
    dsimp [Kseq, A]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_mul_le_self (6*n*(n+1)-1) 5)
  have hmulR : ((Kseq n * 5 : ℕ) : ℝ) ≤ (A:ℝ) := by exact_mod_cast hmul
  dsimp [A] at hmulR ⊢
  norm_num at hmulR ⊢
  nlinarith

private lemma C_div_le_Kseq_add_one (n : ℕ) (hn : 0 < n) :
    (6 * (n:ℝ) * ((n:ℝ)+1)) / 5 ≤ (Kseq n : ℝ) + 1 := by
  let A : ℕ := 6*n*(n+1)-1
  let C : ℕ := 6*n*(n+1)
  have hAdiv : A / 5 < Kseq n + 1 := by
    dsimp [A, Kseq]
    exact Nat.lt_succ_self _
  have hAlt : A < (Kseq n + 1) * 5 := by
    exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 5)).mp hAdiv
  have hCeq : C = A + 1 := by
    dsimp [A, C]
    have hp : 0 < 6*n*(n+1) := by positivity
    omega
  have hCle : C ≤ (Kseq n + 1) * 5 := by omega
  have hCleR : ((C:ℕ):ℝ) ≤ (((Kseq n + 1) * 5 : ℕ):ℝ) := by exact_mod_cast hCle
  dsimp [C] at hCleR
  push_cast at hCleR
  nlinarith

private lemma one_div_Den_floor (n : ℕ) (hn : 0 < n) :
    Int.floor (1 / Den n) = (Kseq n : ℤ) := by
  have hlow := denom_gt_lower_rat n hn
  have hup := denom_lt_upper_rat n hn
  have hCpos : 0 < 6 * (n:ℝ) * ((n:ℝ)+1) := by positivity
  have hApos : 0 < 6 * (n:ℝ) * ((n:ℝ)+1) - 1 := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_self_nonneg ((n:ℝ) - 1)]
  have hLpos : 0 < 5 / (6 * (n:ℝ) * ((n:ℝ)+1)) := by positivity
  have hDpos : 0 < Den n := lt_trans hLpos hlow
  have hrec_up0 := one_div_lt_one_div_of_lt hLpos hlow
  have hrec_up : 1 / Den n < (6 * (n:ℝ) * ((n:ℝ)+1)) / 5 := by
    have hs : 1 / (5 / (6 * (n:ℝ) * ((n:ℝ)+1))) = (6 * (n:ℝ) * ((n:ℝ)+1)) / 5 := by
      field_simp [ne_of_gt hCpos]
    simpa [hs] using hrec_up0
  have hrec_low0 := one_div_lt_one_div_of_lt hDpos hup
  have hrec_low : ((6*n*(n+1)-1 : ℕ) : ℝ) / 5 < 1 / Den n := by
    have hcastA : ((6*n*(n+1)-1 : ℕ) : ℝ) = 6 * (n:ℝ) * ((n:ℝ)+1) - 1 := by
      have hle : 1 ≤ 6*n*(n+1) := by
        have hp : 0 < 6*n*(n+1) := by positivity
        omega
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have hs : 1 / (5 / (6 * (n:ℝ) * ((n:ℝ)+1) - 1)) = (6 * (n:ℝ) * ((n:ℝ)+1) - 1) / 5 := by
      field_simp [ne_of_gt hApos]
    rw [hs] at hrec_low0
    rw [hcastA]
    exact hrec_low0
  rw [Int.floor_eq_iff]
  constructor
  · have hk := Kseq_le_A_div n hn
    have hk' : ((Kseq n : ℤ) : ℝ) ≤ ((6*n*(n+1)-1 : ℕ) : ℝ) / 5 := by
      exact_mod_cast hk
    exact le_trans hk' hrec_low.le
  · have hk := C_div_le_Kseq_add_one n hn
    have hk' : (6 * (n:ℝ) * ((n:ℝ)+1)) / 5 ≤ ((Kseq n : ℤ) : ℝ) + 1 := by
      exact_mod_cast hk
    exact lt_of_lt_of_le hrec_up hk'

private lemma a_eq_Kseq (n : ℕ) (hn : 0 < n) : a n = Kseq n := by
  unfold a
  rw [dif_pos hn]
  rw [bcf_eq_base, bcf_eq_K (n-1)]
  have hn' : n - 1 + 1 = n := by omega
  simp [hn']

/--
At A227581, it is conjectured that a(n) = floor(1/(2*H(n) - H(n^2 + n - 1) - g)),
where H denotes harmonic number and g denotes the Euler-Mascheroni constant.
-/
theorem oeis_227582_conjecture_0 (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor
      (1 / (2 * (↑(harmonic n) : ℝ) -
            (↑(harmonic (n * n + n - 1)) : ℝ) -
            Real.eulerMascheroniConstant))).toNat := by
  have hf := one_div_Den_floor n hn
  have ha := a_eq_Kseq n hn
  dsimp [Den] at hf
  rw [ha, hf]
  simp
