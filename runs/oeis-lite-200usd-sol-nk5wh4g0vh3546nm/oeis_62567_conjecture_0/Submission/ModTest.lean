import FormalConjectures.Util.ProblemImports
open Nat
lemma revmod (D : List ℕ) :
    10 * ofDigits 10 D.reverse ≡ 10 ^ D.length * ofDigits 73 D [MOD 81] := by
  induction D with
  | nil => exact Nat.ModEq.refl 0
  | cons d L ih =>
    have hu : 10 * 73 ≡ 1 [MOD 81] := by norm_num [Nat.ModEq]
    have hs0 := hu.mul (Nat.ModEq.refl (10 ^ L.length * ofDigits 73 L))
    have hs : 10 ^ (L.length + 1) * (73 * ofDigits 73 L) ≡
        10 ^ L.length * ofDigits 73 L [MOD 81] := by
      convert hs0 using 1 <;> ring
    have hd : 10 * 10 ^ L.length * d ≡ 10 * 10 ^ L.length * d [MOD 81] :=
      Nat.ModEq.refl _
    have h := (ih.add hd).trans (hs.symm.add hd)
    simp only [pow_succ] at h
    rw [Nat.ofDigits_reverse_cons]
    simp only [Nat.ofDigits_cons, List.length_cons]
    convert h using 1 <;> ring

lemma revmod9 (D : List ℕ) (hl : D.length = 9) :
    ofDigits 10 D.reverse ≡ 73 * ofDigits 73 D [MOD 81] := by
  have h := revmod D
  rw [hl] at h
  have hc : 10 ^ 9 ≡ 10 * 73 [MOD 81] := by norm_num [Nat.ModEq]
  have hh := h.trans (hc.mul (Nat.ModEq.refl (ofDigits 73 D)))
  have hh' : 10 * ofDigits 10 D.reverse ≡ 10 * (73 * ofDigits 73 D) [MOD 81] := by
    convert hh using 1 <;> ring
  exact Nat.ModEq.cancel_left_of_coprime (by norm_num) hh'

lemma tailmod (A B : ℕ) (h : A ≡ B [MOD 9]) :
    10*A + 73*73*B ≡ A+73*B [MOD 81] := by
  rw [Nat.ModEq] at h ⊢
  omega

lemma combo (D : List ℕ) (hl : D.length ≤ 9) :
    ofDigits 10 D + 73 * ofDigits 73 D ≡ 74 * D.sum [MOD 81] := by
  induction D with
  | nil => exact Nat.ModEq.refl 0
  | cons d L ih =>
    have hlen : L.length ≤ 9 := by simp at hl; omega
    have hi := ih hlen
    have hb : ofDigits 10 L ≡ ofDigits 73 L [MOD 9] :=
      Nat.ofDigits_modEq' 10 73 9 (by norm_num [Nat.ModEq]) L
    have ht := tailmod (ofDigits 10 L) (ofDigits 73 L) hb
    have hh := (Nat.ModEq.refl (74*d)).add (ht.trans hi)
    simp only [Nat.ofDigits_cons, List.sum_cons]
    convert hh using 1 <;> ring

lemma list_nines {D : List ℕ} (hlen : D.length = 9)
    (hdigits : ∀ d ∈ D, d < 10) (hsum : D.sum = 81) :
    D = List.replicate 9 9 := by
  apply List.eq_replicate_iff.2
  refine ⟨hlen, ?_⟩
  intro d hd
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hd
  have h₁ : l₁.sum ≤ l₁.length * 9 := by
    simpa using List.sum_le_card_nsmul l₁ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  have h₂ : l₂.sum ≤ l₂.length * 9 := by
    simpa using List.sum_le_card_nsmul l₂ 9 (by
      intro x hx
      have := hdigits x (by simp [hx])
      omega)
  simp only [List.length_append, List.length_cons, List.length_singleton] at hlen
  simp only [List.sum_append, List.sum_cons, List.sum_singleton] at hsum
  have hdle := hdigits d (by simp)
  omega

def reverse_nat (k : ℕ) : ℕ := ofDigits 10 (digits 10 k).reverse

lemma min81 (j : ℕ) (hj : j < 12345679)
    (hp : j > 0 ∧ 81 ∣ reverse_nat (j * 81)) : False := by
  let m := j * 81
  let L := digits 10 m
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmlt : m < 10 ^ 9 := by
    dsimp [m]
    norm_num
    omega
  have hLlen : L.length ≤ 9 := by
    apply (Nat.digits_length_le_iff (by norm_num) m).2
    exact hmlt
  let D := L ++ List.replicate (9 - L.length) 0
  have hDlen : D.length = 9 := by
    dsimp [D]
    simp
    omega
  have hDdigits : ∀ d ∈ D, d < 10 := by
    intro d hd
    dsimp [D] at hd
    simp at hd
    rcases hd with hd | hd
    · exact Nat.digits_lt_base (by norm_num) hd
    · omega
  have hDm : ofDigits 10 D = m := by
    simp [D, L, Nat.ofDigits_digits]
  have hmdiv : 81 ∣ ofDigits 10 D := by
    rw [hDm]
    exact ⟨j, by simp [m, Nat.mul_comm]⟩
  have hrevdiv : 81 ∣ ofDigits 10 D.reverse := by
    dsimp only [D]
    rw [List.reverse_append, List.reverse_replicate]
    simp only [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate,
      zero_add]
    exact dvd_mul_of_dvd_right hp.2 _
  have hr := revmod9 D hDlen
  have h73mul : 81 ∣ 73 * ofDigits 73 D := by
    rw [← Nat.modEq_zero_iff_dvd] at hrevdiv ⊢
    exact hr.symm.trans hrevdiv
  have h73 : 81 ∣ ofDigits 73 D :=
    (by norm_num : Nat.Coprime 81 73).dvd_of_dvd_mul_left h73mul
  have hc := combo D (by omega)
  have hsumMul : 81 ∣ 74 * D.sum := by
    rw [← Nat.modEq_zero_iff_dvd] at hmdiv h73 ⊢
    exact hc.symm.trans (hmdiv.add ((Nat.ModEq.refl 73).mul h73))
  have hsumdiv : 81 ∣ D.sum :=
    (by norm_num : Nat.Coprime 81 74).dvd_of_dvd_mul_left hsumMul
  have hsumle : D.sum ≤ 81 := by
    have := List.sum_le_card_nsmul D 9 (by
      intro d hd
      have := hDdigits d hd
      omega)
    simpa [hDlen] using this
  rcases hsumdiv with ⟨q, hq⟩
  have hsum_cases : D.sum = 0 ∨ D.sum = 81 := by omega
  rcases hsum_cases with hzero | heq
  · have hz : ∀ d ∈ D, d = 0 := List.sum_eq_zero_iff.mp hzero
    have hDz : D = List.replicate D.length 0 := List.eq_replicate_of_mem hz
    rw [hDz] at hDm
    simp at hDm
    omega
  · have hDnines := list_nines hDlen hDdigits heq
    have : ofDigits 10 D = 999999999 := by rw [hDnines]; norm_num [List.replicate, Nat.ofDigits]
    omega
