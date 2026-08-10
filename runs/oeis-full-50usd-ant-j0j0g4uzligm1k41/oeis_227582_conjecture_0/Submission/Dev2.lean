import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Real

-- Rational inequality for P-monotonicity (artanh upper bound, 3 terms)
lemma ineqP (K : ℝ) (hK : 1 ≤ K) :
    2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2))
    < (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))) := by
  have hK0 : 0 < K := by linarith
  have h1 : 0 < K + 1 := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have h3 : (1 - (1/(2*K+1))^2) = 4*K*(K+1)/(2*K+1)^2 := by
    field_simp; ring
  have hnum : 0 < (40*K^6+120*K^5+182*K^4+164*K^3+76*K^2+14*K+1) := by positivity
  have key : (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)))
      - 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2))
      = (40*K^6+120*K^5+182*K^4+164*K^3+76*K^2+14*K+1)
          / (120*K^4*(K+1)^4*(2*K+1)^5) := by
    rw [h3]
    field_simp
    ring
  have hden : 0 < 120*K^4*(K+1)^4*(2*K+1)^5 := by positivity
  nlinarith [div_pos hnum hden, key]

-- Rational inequality for Q-monotonicity (artanh lower bound, 4 terms)
lemma ineqQ (K : ℝ) (hK : 1 ≤ K) :
    (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))
        + (1/(252*(K+1)^6)-1/(252*K^6)))
    < 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7) := by
  have hK0 : 0 < K := by linarith
  have h1 : 0 < K + 1 := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hnum : 0 < (10612*K^10+53060*K^9+119322*K^8+158928*K^7+138774*K^6+82926*K^5
      +34317*K^4+9720*K^3+1809*K^2+200*K+10) := by positivity
  have key : 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7)
      - (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)) + (1/(252*(K+1)^6)-1/(252*K^6)))
      = (10612*K^10+53060*K^9+119322*K^8+158928*K^7+138774*K^6+82926*K^5
          +34317*K^4+9720*K^3+1809*K^2+200*K+10)
          / (2520*K^6*(K+1)^6*(2*K+1)^7) := by
    field_simp
    ring
  have hden : 0 < 2520*K^6*(K+1)^6*(2*K+1)^7 := by positivity
  nlinarith [div_pos hnum hden, key]

-- log upper bound via artanh, 3 terms
lemma logbound_P (K : ℝ) (hK : 1 ≤ K) :
    Real.log ((K+1)/K) < (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4))) := by
  have hK0 : 0 < K := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hx0 : (0:ℝ) ≤ 1/(2*K+1) := by positivity
  have hx1 : (1:ℝ)/(2*K+1) < 1 := by rw [div_lt_one h2]; linarith
  have hlog := Real.log_div_le_sum_range_add hx0 hx1 3
  have hd : (1:ℝ) - 1/(2*K+1) ≠ 0 := by
    have : (0:ℝ) < 1 - 1/(2*K+1) := by rw [sub_pos]; exact hx1
    linarith
  have hratio : (1 + 1/(2*K+1))/(1 - 1/(2*K+1)) = (K+1)/K := by
    rw [div_eq_div_iff hd hK0.ne']; field_simp; ring
  rw [hratio, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at hlog
  have hub : Real.log ((K+1)/K) ≤ 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5
        + (1/(2*K+1))^7/(1-(1/(2*K+1))^2)) := by
    nlinarith [hlog]
  exact lt_of_le_of_lt hub (ineqP K hK)

-- log lower bound via artanh, 4 terms
lemma logbound_Q (K : ℝ) (hK : 1 ≤ K) :
    (1/(K+1) - (1/(2*(K+1))-1/(2*K)) + (1/(12*(K+1)^2)-1/(12*K^2))
        - (1/(120*(K+1)^4)-1/(120*K^4)) + (1/(252*(K+1)^6)-1/(252*K^6)))
    < Real.log ((K+1)/K) := by
  have hK0 : 0 < K := by linarith
  have h2 : 0 < 2*K+1 := by linarith
  have hx0 : (0:ℝ) ≤ 1/(2*K+1) := by positivity
  have hx1 : (1:ℝ)/(2*K+1) < 1 := by rw [div_lt_one h2]; linarith
  have hlog := Real.sum_range_le_log_div hx0 hx1 4
  have hd : (1:ℝ) - 1/(2*K+1) ≠ 0 := by
    have : (0:ℝ) < 1 - 1/(2*K+1) := by rw [sub_pos]; exact hx1
    linarith
  have hratio : (1 + 1/(2*K+1))/(1 - 1/(2*K+1)) = (K+1)/K := by
    rw [div_eq_div_iff hd hK0.ne']; field_simp; ring
  rw [hratio, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hlog
  have hlb : 2*(1/(2*K+1) + (1/(2*K+1))^3/3 + (1/(2*K+1))^5/5 + (1/(2*K+1))^7/7)
      ≤ Real.log ((K+1)/K) := by
    nlinarith [hlog]
  exact lt_of_lt_of_le (ineqQ K hK) hlb

noncomputable def Pseq (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - 1/(2*n) + 1/(12*n^2) - 1/(120*n^4)

noncomputable def Qseq (n : ℕ) : ℝ := Pseq n + 1/(252*n^6)

lemma Pseq_step (k : ℕ) (hk : 1 ≤ k) : Pseq k < Pseq (k+1) := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : ((k:ℝ)) ≠ 0 := by positivity
  have hk1' : ((k:ℝ)+1) ≠ 0 := by positivity
  have hh : (harmonic (k+1) : ℝ) = (harmonic k : ℝ) + 1/((k:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have hl : Real.log (((k:ℝ)+1)/(k:ℝ)) = Real.log ((k:ℝ)+1) - Real.log (k:ℝ) :=
    Real.log_div hk1' hk0
  have key := logbound_P (k:ℝ) hk1
  have hP : Pseq (k+1) - Pseq k =
      (1/((k:ℝ)+1) - (1/(2*((k:ℝ)+1))-1/(2*(k:ℝ))) + (1/(12*((k:ℝ)+1)^2)-1/(12*(k:ℝ)^2))
        - (1/(120*((k:ℝ)+1)^4)-1/(120*(k:ℝ)^4))) - Real.log (((k:ℝ)+1)/(k:ℝ)) := by
    simp only [Pseq]
    push_cast [hh]
    rw [hl]
    ring
  linarith [hP, key]

lemma Qseq_step (k : ℕ) (hk : 1 ≤ k) : Qseq (k+1) < Qseq k := by
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : ((k:ℝ)) ≠ 0 := by positivity
  have hk1' : ((k:ℝ)+1) ≠ 0 := by positivity
  have hh : (harmonic (k+1) : ℝ) = (harmonic k : ℝ) + 1/((k:ℝ)+1) := by
    rw [harmonic_succ]; push_cast; ring
  have hl : Real.log (((k:ℝ)+1)/(k:ℝ)) = Real.log ((k:ℝ)+1) - Real.log (k:ℝ) :=
    Real.log_div hk1' hk0
  have key := logbound_Q (k:ℝ) hk1
  have hQ : Qseq (k+1) - Qseq k =
      (1/((k:ℝ)+1) - (1/(2*((k:ℝ)+1))-1/(2*(k:ℝ))) + (1/(12*((k:ℝ)+1)^2)-1/(12*(k:ℝ)^2))
        - (1/(120*((k:ℝ)+1)^4)-1/(120*(k:ℝ)^4)) + (1/(252*((k:ℝ)+1)^6)-1/(252*(k:ℝ)^6)))
        - Real.log (((k:ℝ)+1)/(k:ℝ)) := by
    simp only [Qseq, Pseq]
    push_cast [hh]
    rw [hl]
    ring
  linarith [hQ, key]

open Filter Topology in
lemma tendsto_Pseq : Tendsto Pseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have t1 : Filter.Tendsto (fun n:ℕ => 1/(n:ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hcont : Continuous (fun t:ℝ => -t/2 + t^2/12 - t^4/120) := by fun_prop
  have hc0 := (hcont.tendsto (0:ℝ)).comp t1
  rw [show (-0/2 + 0^2/12 - 0^4/120 : ℝ) = 0 by norm_num] at hc0
  have hsum := Real.tendsto_harmonic_sub_log.add hc0
  rw [add_zero] at hsum
  apply hsum.congr
  intro n
  simp only [Pseq, Function.comp]
  ring

open Filter Topology in
lemma tendsto_Qseq : Tendsto Qseq atTop (𝓝 Real.eulerMascheroniConstant) := by
  have t1 : Filter.Tendsto (fun n:ℕ => 1/(n:ℝ)) Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hcont : Continuous (fun t:ℝ => -t/2 + t^2/12 - t^4/120 + t^6/252) := by fun_prop
  have hc0 := (hcont.tendsto (0:ℝ)).comp t1
  rw [show (-0/2 + 0^2/12 - 0^4/120 + 0^6/252 : ℝ) = 0 by norm_num] at hc0
  have hsum := Real.tendsto_harmonic_sub_log.add hc0
  rw [add_zero] at hsum
  apply hsum.congr
  intro n
  simp only [Qseq, Pseq, Function.comp]
  ring

open Filter Topology in
lemma Pseq_lt_g (n : ℕ) (hn : 1 ≤ n) : Pseq n < Real.eulerMascheroniConstant := by
  have hmono : Monotone (fun m => Pseq (m+1)) :=
    monotone_nat_of_le_succ (fun m => (Pseq_step (m+1) (Nat.le_add_left 1 m)).le)
  have htend : Tendsto (fun m => Pseq (m+1)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_Pseq.comp (tendsto_add_atTop_nat 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h1 : Pseq (m+1) < Pseq (m+2) := Pseq_step (m+1) (Nat.le_add_left 1 m)
  have h2 : Pseq (m+2) ≤ Real.eulerMascheroniConstant := hmono.ge_of_tendsto htend (m+1)
  linarith

open Filter Topology in
lemma g_lt_Qseq (n : ℕ) (hn : 1 ≤ n) : Real.eulerMascheroniConstant < Qseq n := by
  have hanti : Antitone (fun m => Qseq (m+1)) :=
    antitone_nat_of_succ_le (fun m => (Qseq_step (m+1) (Nat.le_add_left 1 m)).le)
  have htend : Tendsto (fun m => Qseq (m+1)) atTop (𝓝 Real.eulerMascheroniConstant) :=
    tendsto_Qseq.comp (tendsto_add_atTop_nat 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h1 : Qseq (m+2) < Qseq (m+1) := Qseq_step (m+1) (Nat.le_add_left 1 m)
  have h2 : Real.eulerMascheroniConstant ≤ Qseq (m+2) := hanti.le_of_tendsto htend (m+1)
  linarith
