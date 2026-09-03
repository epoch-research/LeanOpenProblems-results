import Submission.ArithmeticPatternObstruction

/-! Fixed-modulus refinements of the pattern obstruction. Not a settlement. -/

namespace Erdos406Work

lemma good_add_shifted {a b L : ℕ} (ha : a < 3 ^ L)
    (hga : Nat.digits 3 a ⊆ [0, 1]) (hgb : Nat.digits 3 b ⊆ [0, 1]) :
    Nat.digits 3 (a + 3 ^ L * b) ⊆ [0, 1] := by
  let w := ternaryPrefix L a ++ Nat.digits 3 b
  have hw : w ⊆ [0, 1] := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · have hh := ternaryPrefix_lt_two hga d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · exact hgb hd
  have hv : Nat.ofDigits 3 w = a + 3 ^ L * b := by
    rw [Nat.ofDigits_append, ofDigits_ternaryPrefix, ternaryPrefix_length,
      Nat.ofDigits_digits, Nat.mod_eq_of_lt ha]
  rw [← hv]
  exact good_ofDigits hw

/-- For a modulus with known three-part, the low ternary digits are the only
obstruction to finding a good representative in a specified residue class. -/
lemma good_representative_mod_three_part (a b r : ℕ) (hb : Nat.Coprime 3 b)
    (hr : Nat.digits 3 (r % 3 ^ a) ⊆ [0, 1]) :
    ∃ n : ℕ, Nat.digits 3 n ⊆ [0, 1] ∧ Nat.ModEq (3 ^ a * b) n r := by
  obtain ⟨v, hgv, hv⟩ := good_representative_mod hb (r / 3 ^ a)
  refine ⟨r % 3 ^ a + 3 ^ a * v,
    good_add_shifted (Nat.mod_lt _ (by positivity)) hr hgv, ?_⟩
  have hh := (hv.mul_left' (3 ^ a)).add_left (r % 3 ^ a)
  simpa only [Nat.mod_add_div] using hh

lemma good_add_top_power {n c : ℕ} (hn : Nat.digits 3 n ⊆ [0, 1])
    (hc : (Nat.digits 3 n).length ≤ c) : Nat.digits 3 (3 ^ c + n) ⊆ [0, 1] := by
  rw [Nat.add_comm]
  have h := Nat.lt_base_pow_length_digits (b := 3) (m := n) (by decide)
  have hlt : n < 3 ^ c := h.trans_le (Nat.pow_le_pow_right (by decide) hc)
  simpa only [mul_one] using good_add_shifted hlt hn (by decide +kernel : Nat.digits 3 1 ⊆ [0, 1])

lemma good_top_term_residue_progression (a b r : ℕ) (hb : Nat.Coprime 3 b)
    (hr : Nat.digits 3 (r % 3 ^ a) ⊆ [0, 1]) :
    ∃ v c₀ T : ℕ, 0 < T ∧ Nat.digits 3 v ⊆ [0, 1] ∧
      ∀ j : ℕ, Nat.ModEq (3 ^ a * b) (3 ^ (c₀ + T * j) + v) r := by
  have hbpos : 0 < b := by
    by_contra hh
    have hz : b = 0 := by omega
    simp [hz] at hb
  let q := 3 ^ a * b
  have hqpos : 0 < q := by dsimp [q]; positivity
  let T := b.totient
  have hT : 0 < T := Nat.totient_pos.mpr hbpos
  let c₀ := T * a
  have hac : a ≤ c₀ := Nat.le_mul_of_pos_left _ hT
  let p := 3 ^ c₀ % q
  have hplt : p < q := Nat.mod_lt _ hqpos
  have hpowmod : ∀ j : ℕ, Nat.ModEq q (3 ^ (c₀ + T * j)) (3 ^ c₀) := by
    intro j
    apply (Nat.modEq_and_modEq_iff_modEq_mul (hb.pow_left a)).mp
    constructor
    · have hleft : 3 ^ a ∣ 3 ^ (c₀ + T * j) := pow_dvd_pow _ (by omega)
      have hright : 3 ^ a ∣ 3 ^ c₀ := pow_dvd_pow _ hac
      exact hleft.modEq_zero_nat.trans hright.modEq_zero_nat.symm
    · have hh := ((Nat.ModEq.pow_totient hb).pow j).mul_left (3 ^ c₀)
      simpa only [← pow_mul, one_pow, mul_one, ← pow_add] using hh
  have hp0 : Nat.ModEq (3 ^ a) p 0 := by
    have hh := (Nat.mod_modEq (3 ^ c₀) q).of_dvd (dvd_mul_right (3 ^ a) b)
    exact hh.trans (pow_dvd_pow 3 hac).modEq_zero_nat
  have hq0 : Nat.ModEq (3 ^ a) q 0 := (dvd_mul_right (3 ^ a) b).modEq_zero_nat
  have hr' : Nat.ModEq (3 ^ a) (q + r - p) r := by
    have hsum : Nat.ModEq (3 ^ a) (q + r) r := by simpa using hq0.add (Nat.ModEq.refl r)
    have hh := hsum.sub (by omega : p ≤ q + r) (by omega : 0 ≤ r) hp0
    simpa only [Nat.sub_zero] using hh
  obtain ⟨v, hgv, hv⟩ := good_representative_mod_three_part a b (q + r - p) hb
    (by rw [hr']; exact hr)
  refine ⟨v, c₀, T, hT, hgv, ?_⟩
  intro j
  have hcp : Nat.ModEq q (3 ^ (c₀ + T * j)) p :=
    (hpowmod j).trans (Nat.mod_modEq (3 ^ c₀) q).symm
  have hh := hcp.add hv
  have he : p + (q + r - p) = q + r := by omega
  rw [he] at hh
  exact hh.trans (by simp [Nat.ModEq])

lemma prescribed_prefix_predecessor (A Q a b r B E : ℕ)
    (hA : 0 < A) (hQ : 0 < Q) (hcopQ : Nat.Coprime 3 Q) (hb : Nat.Coprime 3 b)
    (hlo : A * Q < 3 ^ E) (hhi : 3 ^ E < (A + 1) * Q)
    (hr : Nat.digits 3 (Q * r % 3 ^ a) ⊆ [0, 1]) :
    ∃ n L : ℕ, B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (Q * n) ⊆ [0, 1] ∧ Nat.ModEq (3 ^ a * b) n r := by
  obtain ⟨v, c₀, T, hT, hgoodv, hperiod⟩ :=
    good_top_term_residue_progression a (Q * b) (Q * r) (hcopQ.mul_right hb) hr
  let q := 3 ^ a * b
  let c := c₀ + T * (E + B + v + (Nat.digits 3 v).length + 1)
  have hcle : E + B + v + (Nat.digits 3 v).length + 1 ≤ c := by
    exact (Nat.le_mul_of_pos_left _ hT).trans (Nat.le_add_left _ _)
  have hc : (Nat.digits 3 v).length ≤ c := by omega
  have htarget : Nat.ModEq (Q * q) (3 ^ c + v) (Q * r) := by
    have hh := hperiod (E + B + v + (Nat.digits 3 v).length + 1)
    have he : 3 ^ a * (Q * b) = Q * q := by dsimp [q]; ring
    rwa [he] at hh
  have hd : Q ∣ 3 ^ c + v :=
    (htarget.dvd_iff (dvd_mul_right Q q)).mpr (dvd_mul_right Q r)
  obtain ⟨n, hn⟩ := hd
  have hnmod : Nat.ModEq q n r := by
    rw [hn] at htarget
    exact Nat.ModEq.mul_left_cancel' (ne_of_gt hQ) htarget
  let L := c - E
  have hLB : B < L := by dsimp [L]; omega
  have hLv : v < L := by dsimp [L]; omega
  have hpow : 3 ^ c = 3 ^ E * 3 ^ L := by
    rw [← pow_add]
    congr 1
    dsimp [L]
    omega
  have hvL : v < 3 ^ L := hLv.trans (Nat.lt_pow_self (by decide))
  have hnlo : A * 3 ^ L ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := Q) _ hQ
    calc
      Q * (A * 3 ^ L) = (A * Q) * 3 ^ L := by ring
      _ ≤ 3 ^ E * 3 ^ L := Nat.mul_le_mul_right _ (le_of_lt hlo)
      _ ≤ Q * n := by rw [← hn, ← hpow]; omega
  have hnhi : n < (A + 1) * 3 ^ L := by
    apply Nat.lt_of_mul_lt_mul_left (a := Q)
    have hh := Nat.mul_le_mul_right (3 ^ L) (Nat.succ_le_of_lt hhi)
    calc
      Q * n = 3 ^ E * 3 ^ L + v := by rw [← hn, hpow]
      _ < (3 ^ E + 1) * 3 ^ L := by nlinarith
      _ ≤ ((A + 1) * Q) * 3 ^ L := hh
      _ = Q * ((A + 1) * 3 ^ L) := by ring
  have hnB : B < n := by
    have hh : L < 3 ^ L := Nat.lt_pow_self (by decide)
    have hAn : 3 ^ L ≤ A * 3 ^ L := Nat.le_mul_of_pos_left _ hA
    omega
  refine ⟨n, L, hnB, Nat.div_eq_of_lt_le hnlo hnhi, ?_, hnmod⟩
  rw [← hn]
  exact good_add_top_power hgoodv hc

lemma reciprocal_four_power_prefix_in_progression (A s D t₀ : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hD : 0 < D) :
    ∃ j E : ℕ, 0 < j ∧ A * 4 ^ (s * (t₀ + D * j)) < 3 ^ E ∧
      3 ^ E < (A + 1) * 4 ^ (s * (t₀ + D * j)) := by
  obtain ⟨j, E, hj, hlo, hhi⟩ := reciprocal_four_power_prefix
    (A * 4 ^ (s * t₀)) (s * D) (by positivity) (Nat.mul_pos hs hD)
  have he : 4 ^ (s * (t₀ + D * j)) = 4 ^ (s * t₀) * 4 ^ ((s * D) * j) := by
    rw [← pow_add]
    congr 1
    ring
  refine ⟨j, E, hj, ?_, ?_⟩
  · rw [he, ← mul_assoc]
    exact hlo
  · apply hhi.trans_le
    rw [he, ← mul_assoc]
    apply Nat.mul_le_mul_right
    have hp : 1 ≤ 4 ^ (s * t₀) := Nat.one_le_pow _ _ (by decide)
    nlinarith

lemma arbitrary_prefix_can_disappear_mod_class (A s a b r e B : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hb : Nat.Coprime 3 b)
    (hclass : Nat.ModEq (3 ^ a) r (4 ^ (s * e))) :
    ∃ t n L : ℕ, 0 < t ∧ B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq (3 ^ a * b) n r := by
  let t₀ := e * (3 ^ a - 1)
  obtain ⟨j, E, hj, hlo, hhi⟩ := reciprocal_four_power_prefix_in_progression A s (3 ^ a) t₀
    hA hs (by positivity)
  let t := t₀ + 3 ^ a * j
  have ht : 0 < t := by dsimp [t]; positivity
  have he : s * t + s * e = 3 ^ a * (s * (e + j)) := by
    have hp : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by decide)
    have hd : 3 ^ a - 1 + 1 = 3 ^ a := Nat.sub_add_cancel hp
    dsimp [t, t₀]
    calc
      s * (e * (3 ^ a - 1) + 3 ^ a * j) + s * e =
          s * e * (3 ^ a - 1 + 1) + 3 ^ a * (s * j) := by ring
      _ = 3 ^ a * (s * (e + j)) := by rw [hd]; ring
  have hpow : Nat.ModEq (3 ^ (a + 1)) (4 ^ (s * t + s * e)) 1 :=
    (four_pow_mod_eq_one_iff a _).mpr ⟨s * (e + j), he⟩
  have hpowlow := hpow.of_dvd (pow_dvd_pow 3 (by omega : a ≤ a + 1))
  have hr : Nat.digits 3 (4 ^ (s * t) * r % 3 ^ a) ⊆ [0, 1] := by
    rw [hclass.mul_left (4 ^ (s * t)), ← pow_add, hpowlow]
    by_cases ha : a = 0
    · simp [ha]
    · rw [Nat.mod_eq_of_lt (one_lt_pow₀ (by decide : 1 < 3) ha)]
      decide +kernel
  obtain ⟨n, L, hnB, hlead, hgood, hmod⟩ := prescribed_prefix_predecessor
    A (4 ^ (s * t)) a b r B E hA (by positivity)
    ((by decide : Nat.Coprime 3 4).pow_right _) hb hlo hhi hr
  exact ⟨t, n, L, ht, hnB, hlead, hgood, hmod⟩

/-- All fixed moduli can be handled for a power residue in the zero stride
class. As in the earlier construction, this does not assert that the
predecessor is a power of two. -/
lemma arbitrary_prefix_can_disappear_full_mod (A s q e B : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hq : 0 < q) :
    ∃ t n L : ℕ, 0 < t ∧ B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n (4 ^ (s * e)) := by
  obtain ⟨a, b, hbn, hqeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (ne_of_gt hq) 3 (by decide)
  have hb : Nat.Coprime 3 b := (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hbn
  rw [hqeq]
  exact arbitrary_prefix_can_disappear_mod_class A s a b (4 ^ (s * e)) e B hA hs hb rfl

lemma arbitrary_nonpower_prefix_can_disappear_full_mod (A s q e B : ℕ)
    (hA : 0 < A) (hs : 0 < s) (hq : 0 < q) :
    ∃ t n L : ℕ, 0 < t ∧ B < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n (4 ^ (s * e)) ∧
      ¬ n.isPowerOfTwo := by
  obtain ⟨a, b, hbn, hqeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (ne_of_gt hq) 3 (by decide)
  have hb : Nat.Coprime 3 b := (by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hbn
  obtain ⟨p, hpq, hp⟩ := Nat.exists_infinite_primes (q + 4)
  have hp3 : 3 < p := by omega
  have hcpq : Nat.Coprime p q := Nat.coprime_of_lt_prime (ne_of_gt hq) (by omega) hp
  have hc3p : Nat.Coprime 3 p :=
    (Nat.coprime_of_lt_prime (by decide : 3 ≠ 0) hp3 hp).symm
  let R := 4 ^ (s * e) * p ^ q.totient
  have hR : Nat.ModEq q R (4 ^ (s * e)) := by
    have hh := (Nat.ModEq.pow_totient hcpq).mul_left (4 ^ (s * e))
    simpa only [mul_one] using hh
  have hpR : p ∣ R := by
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self p (ne_of_gt (Nat.totient_pos.mpr hq))
  have hclass : Nat.ModEq (3 ^ a) R (4 ^ (s * e)) := by
    apply hR.of_dvd
    rw [hqeq]
    exact dvd_mul_right _ _
  obtain ⟨t, n, L, ht, hnB, hlead, hgood, hmod⟩ :=
    arbitrary_prefix_can_disappear_mod_class A s a (b * p) R e B hA hs
      (hb.mul_right hc3p) hclass
  have he : 3 ^ a * (b * p) = q * p := by rw [hqeq]; ring
  rw [he] at hmod
  have hnq : Nat.ModEq q n (4 ^ (s * e)) :=
    (hmod.of_dvd (dvd_mul_right q p)).trans hR
  have hpn : p ∣ n := (hmod.dvd_iff (dvd_mul_left p q)).mpr hpR
  refine ⟨t, n, L, ht, hnB, hlead, hgood, hnq, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk] at hpn
  have h2 := hp.dvd_of_dvd_pow hpn
  have hle := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

lemma arbitrary_nonpower_block_can_disappear_full_mod (w : List ℕ) (hw : ∀ d ∈ w, d < 3)
    (s q e B : ℕ) (hs : 0 < s) (hq : 0 < q) :
    ∃ t n : ℕ, 0 < t ∧ B < n ∧ w <:+: Nat.digits 3 n ∧
      Nat.digits 3 (4 ^ (s * t) * n) ⊆ [0, 1] ∧ Nat.ModEq q n (4 ^ (s * e)) ∧
      ¬ n.isPowerOfTwo := by
  let A := Nat.ofDigits 3 (w ++ [1])
  have hA : 0 < A := by
    dsimp [A]
    rw [Nat.ofDigits_append]
    simp only [Nat.ofDigits_singleton, mul_one]
    positivity
  have hdA : Nat.digits 3 A = w ++ [1] := by
    apply Nat.digits_ofDigits 3 (by decide)
    · intro d hd
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with hd | rfl
      · exact hw d hd
      · decide
    · intro h
      simp
  obtain ⟨t, n, L, ht, hnB, hnA, hgood, hmod, hnp⟩ :=
    arbitrary_nonpower_prefix_can_disappear_full_mod A s q e B hA hs hq
  have hdrop : (Nat.digits 3 n).drop L = w ++ [1] := by
    have hh := congrArg (Nat.digits 3) hnA
    rwa [digits_div_three_pow, hdA] at hh
  refine ⟨t, n, ht, hnB, ?_, hgood, hmod, hnp⟩
  refine ⟨(Nat.digits 3 n).take L, [1], ?_⟩
  rw [List.append_assoc, ← hdrop, List.take_append_drop]

/-- Even allowing arbitrary fixed congruence tests does not repair finite
substring-presence certificates for all powers. The zero stride class is
necessary: a different single stride class may already be excluded by a
fixed low ternary digit. -/
lemma finite_pattern_full_arithmetic_certificate_no_power_seed (P : ℕ → Prop)
    (F : List (List ℕ)) (hF : ∀ w ∈ F, ∀ d ∈ w, d < 3)
    (q : ℕ) (hq : 0 < q)
    (B K s E : ℕ) (hs : 0 < s) (hKE : K ≤ E) (hBE : B < 4 ^ E) (hSE : s ∣ E)
    (hsame : ∀ n m : ℕ, B < n → B < m → 4 ^ K ∣ n → 4 ^ K ∣ m → Nat.ModEq q n m →
      (∀ w ∈ F, (w <:+: Nat.digits 3 n ↔ w <:+: Nat.digits 3 m)) → P n → P m)
    (hmul : ∀ n : ℕ, B < n → 4 ^ K ∣ n → P n → P (4 ^ s * n))
    (hsafe : ∀ n : ℕ, B < n → 4 ^ K ∣ n → Nat.digits 3 n ⊆ [0, 1] → ¬ P n) :
    ¬ P (4 ^ E) := by
  intro hseed
  obtain ⟨e, he⟩ := hSE
  have hflat : ∀ d ∈ F.flatten, d < 3 := by
    intro d hd
    obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
    exact hF w hw d hdw
  have hpowB (j : ℕ) : B < 4 ^ (E + s * j) :=
    hBE.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hpowK (j : ℕ) : 4 ^ K ∣ 4 ^ (E + s * j) := pow_dvd_pow 4 (by omega)
  have hiterPow : ∀ j : ℕ, P (4 ^ (E + s * j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      have hh := hmul _ (hpowB j) (hpowK j) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  obtain ⟨j, _, hwordPow⟩ := power_in_progression_contains_block F.flatten hflat E s 0 hs
  obtain ⟨t, m, ht, hmB, hwordM, hgood, hmod, _⟩ :=
    arbitrary_nonpower_block_can_disappear_full_mod F.flatten hflat s (q * 4 ^ K)
      (e + j) B hs (by positivity)
  have hexp : s * (e + j) = E + s * j := by rw [he]; ring
  rw [hexp] at hmod
  have hmK : 4 ^ K ∣ m :=
    (hmod.dvd_iff (dvd_mul_left (4 ^ K) q)).mpr (hpowK j)
  have hmQ : Nat.ModEq q (4 ^ (E + s * j)) m :=
    (hmod.of_dvd (dvd_mul_right q (4 ^ K))).symm
  have hPm : P m := by
    apply hsame (4 ^ (E + s * j)) m (hpowB j) hmB (hpowK j) hmK hmQ _ (hiterPow j)
    intro w hw
    have hh := infix_flatten_of_mem hw
    exact ⟨fun _ => hh.trans hwordM, fun _ => hh.trans hwordPow⟩
  have hmpos : 0 < m := by omega
  have horbitB (i : ℕ) : B < 4 ^ (s * i) * m :=
    hmB.trans_le (Nat.le_mul_of_pos_left m (by positivity))
  have horbitK (i : ℕ) : 4 ^ K ∣ 4 ^ (s * i) * m := dvd_mul_of_dvd_right hmK _
  have hiterM : ∀ i : ℕ, P (4 ^ (s * i) * m) := by
    intro i
    induction i with
    | zero => simpa using hPm
    | succ i ih =>
      have hh := hmul _ (horbitB i) (horbitK i) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  exact hsafe _ (horbitB t) (horbitK t) hgood (hiterM t)


lemma fixed_leading_digits_of_quotient {n m L R : ℕ}
    (hdiv : n / 3 ^ L = m) (hlen : R ≤ (Nat.digits 3 m).length) :
    (Nat.digits 3 n).reverse.take R = (Nat.digits 3 m).reverse.take R := by
  have hdrop : (Nat.digits 3 n).drop L = Nat.digits 3 m := by
    rw [← digits_div_three_pow, hdiv]
  have hword : Nat.digits 3 n = (Nat.digits 3 n).take L ++ Nat.digits 3 m := by
    rw [← hdrop, List.take_append_drop]
  rw [hword, List.reverse_append, List.take_append_of_le_length]
  simpa using hlen

/-- Fixed leading and trailing tests, arbitrary fixed congruences, and finitely
many unanchored substring-presence tests still cannot supply this invariant.
This does not cover modular pattern counts or general regular languages. -/
lemma finite_pattern_endpoint_arithmetic_certificate_no_power_seed (P : ℕ → Prop)
    (F : List (List ℕ)) (hF : ∀ w ∈ F, ∀ d ∈ w, d < 3)
    (R q : ℕ) (hq : 0 < q)
    (B K s E : ℕ) (hs : 0 < s) (hKE : K ≤ E) (hBE : B < 4 ^ E) (hSE : s ∣ E)
    (hsame : ∀ n m : ℕ, B < n → B < m → 4 ^ K ∣ n → 4 ^ K ∣ m → Nat.ModEq q n m →
      (Nat.digits 3 n).reverse.take R = (Nat.digits 3 m).reverse.take R →
      (∀ w ∈ F, (w <:+: Nat.digits 3 n ↔ w <:+: Nat.digits 3 m)) → P n → P m)
    (hmul : ∀ n : ℕ, B < n → 4 ^ K ∣ n → P n → P (4 ^ s * n))
    (hsafe : ∀ n : ℕ, B < n → 4 ^ K ∣ n → Nat.digits 3 n ⊆ [0, 1] → ¬ P n) :
    ¬ P (4 ^ E) := by
  intro hseed
  obtain ⟨e, he⟩ := hSE
  have hflat : ∀ d ∈ F.flatten, d < 3 := by
    intro d hd
    obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
    exact hF w hw d hdw
  have hpowB (j : ℕ) : B < 4 ^ (E + s * j) :=
    hBE.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hpowK (j : ℕ) : 4 ^ K ∣ 4 ^ (E + s * j) := pow_dvd_pow 4 (by omega)
  have hiterPow : ∀ j : ℕ, P (4 ^ (E + s * j)) := by
    intro j
    induction j with
    | zero => simpa using hseed
    | succ j ih =>
      have hh := hmul _ (hpowB j) (hpowK j) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  have hblock : ∀ d ∈ F.flatten ++ List.replicate R 0, d < 3 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hflat d hd
    · have hh := (List.mem_replicate.mp hd).2
      omega
  obtain ⟨j, _, hcontains⟩ := power_in_progression_contains_block
    (F.flatten ++ List.replicate R 0) hblock E s 0 hs
  have hwordPow : F.flatten <:+: Nat.digits 3 (4 ^ (E + s * j)) :=
    (show F.flatten <:+: F.flatten ++ List.replicate R 0 from ⟨[], List.replicate R 0, by simp⟩).trans hcontains
  have hlenPow : R ≤ (Nat.digits 3 (4 ^ (E + s * j))).length := by
    have hh := hcontains.length_le
    simp only [List.length_append, List.length_replicate] at hh
    omega
  obtain ⟨t, m, L, ht, hmB, hquot, hgood, hmod, _⟩ :=
    arbitrary_nonpower_prefix_can_disappear_full_mod (4 ^ (E + s * j)) s (q * 4 ^ K)
      (e + j) B (by positivity) hs (by positivity)
  have hdrop : (Nat.digits 3 m).drop L = Nat.digits 3 (4 ^ (E + s * j)) := by
    rw [← digits_div_three_pow, hquot]
  have hsuf : Nat.digits 3 (4 ^ (E + s * j)) <:+ Nat.digits 3 m := by
    refine ⟨(Nat.digits 3 m).take L, ?_⟩
    rw [← hdrop, List.take_append_drop]
  have hwordM : F.flatten <:+: Nat.digits 3 m := hwordPow.trans hsuf.isInfix
  have hleading : (Nat.digits 3 (4 ^ (E + s * j))).reverse.take R =
      (Nat.digits 3 m).reverse.take R := (fixed_leading_digits_of_quotient hquot hlenPow).symm
  have hexp : s * (e + j) = E + s * j := by rw [he]; ring
  rw [hexp] at hmod
  have hmK : 4 ^ K ∣ m :=
    (hmod.dvd_iff (dvd_mul_left (4 ^ K) q)).mpr (hpowK j)
  have hmQ : Nat.ModEq q (4 ^ (E + s * j)) m :=
    (hmod.of_dvd (dvd_mul_right q (4 ^ K))).symm
  have hPm : P m := by
    apply hsame (4 ^ (E + s * j)) m (hpowB j) hmB (hpowK j) hmK hmQ hleading _ (hiterPow j)
    intro w hw
    have hh := infix_flatten_of_mem hw
    exact ⟨fun _ => hh.trans hwordM, fun _ => hh.trans hwordPow⟩
  have hmpos : 0 < m := by omega
  have horbitB (i : ℕ) : B < 4 ^ (s * i) * m :=
    hmB.trans_le (Nat.le_mul_of_pos_left m (by positivity))
  have horbitK (i : ℕ) : 4 ^ K ∣ 4 ^ (s * i) * m := dvd_mul_of_dvd_right hmK _
  have hiterM : ∀ i : ℕ, P (4 ^ (s * i) * m) := by
    intro i
    induction i with
    | zero => simpa using hPm
    | succ i ih =>
      have hh := hmul _ (horbitB i) (horbitK i) ih
      simpa only [Nat.mul_succ, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  exact hsafe _ (horbitB t) (horbitK t) hgood (hiterM t)


#print axioms good_representative_mod_three_part
#print axioms good_top_term_residue_progression
#print axioms prescribed_prefix_predecessor
#print axioms arbitrary_prefix_can_disappear_full_mod
#print axioms arbitrary_nonpower_prefix_can_disappear_full_mod
#print axioms finite_pattern_full_arithmetic_certificate_no_power_seed
#print axioms finite_pattern_endpoint_arithmetic_certificate_no_power_seed
end Erdos406Work
