import Submission.Shifted
open Nat Finset BigOperators Int

lemma shifted_paired_sum_dvd
    {p lev B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) (hjA : j ≤ B+Y)
    (c : ℕ → ℤ) (hc0 : c 0 = 0)
    (hanti : ∀ d, d ≤ j → c (j-d) = -c d) :
    ((p : ℤ)^(3*(lev+1))) ∣
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ) := by
  let M : ℕ := p^(3*(lev+1))
  let f : ℕ → ZMod M := fun d =>
    (((p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
      (chooseSub (B+Y-j) B d : ℤ) : ℤ) : ZMod M)
  have hsum : ∑ d ∈ Finset.range (j+1), f d = 0 := by
    apply Finset.sum_involution (fun d _ => j-d)
    · intro d hdmem
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      let e := j-d
      have hej : e ≤ j := Nat.sub_le _ _
      by_cases hd0 : d = 0
      · subst d
        have hcj : c j = 0 := by
          have ha := hanti 0 (Nat.zero_le j)
          simpa [hc0] using ha
        simp [f, hc0, hcj]
      by_cases he0 : e = 0
      · have hce : c e = 0 := by simpa [he0] using hc0
        have hcd : c d = 0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl, hce] at ha
          omega
        simp [f, hcd, hce, e]
      by_cases hde : d = e
      · have hcd : c d = 0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl, ← hde] at ha
          omega
        have hflip : j-d=d := by simpa [e] using hde.symm
        simp [f, hcd, hflip]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hepos : 0 < e := Nat.pos_of_ne_zero he0
        have hsumde : d+e=j := by dsimp [e]; omega
        have hdiv := paired_shifted_choose_term_dvd hp hp5 hB hY hdpos hepos hde
          (show d+e ≤ B+Y by omega)
        rw [hsumde] at hdiv
        have hdiv' : ((p : ℤ)^(3*(lev+1))) ∣
            c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ) - chooseSub (B+Y-j) B e)) := by
          convert dvd_mul_of_dvd_right hdiv (c d) using 1 <;> ring
        have hz : ((c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ) - chooseSub (B+Y-j) B e)) : ℤ) : ZMod M) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          simpa [M] using hdiv'
        have ha := hanti d hdj
        change f d + f e = 0
        dsimp [f]
        rw [ha]
        rw [← Int.cast_add]
        convert hz using 1 <;> ring
    · intro d hdmem hfd
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      intro heq
      have hc : c d = 0 := by
        have ha := hanti d hdj
        rw [heq] at ha
        omega
      simp [f, hc] at hfd
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
  have hz : (((∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ)) : ℤ) : ZMod M) = 0 := by
    simpa [f] using hsum
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  simpa [M] using hz


lemma shifted_paired_sum_dvd_total
    {p L B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hprod : ((p : ℤ)^L) ∣ (B : ℤ)*Y*((Y : ℤ)-B)) (hjA : j ≤ B+Y)
    (c : ℕ → ℤ) (hc0 : c 0 = 0)
    (hanti : ∀ d, d ≤ j → c (j-d) = -c d) :
    ((p : ℤ)^(L+3)) ∣
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
          (chooseSub (B+Y-j) B d : ℤ) := by
  let M : ℕ := p^(L+3)
  let f : ℕ → ZMod M := fun d =>
    (((p : ℤ)^j * c d * ((B+Y).choose j : ℤ) *
      (chooseSub (B+Y-j) B d : ℤ) : ℤ) : ZMod M)
  have hsum : ∑ d ∈ Finset.range (j+1), f d = 0 := by
    apply Finset.sum_involution (fun d _ => j-d)
    · intro d hdmem
      have hdj : d ≤ j := by simpa [Finset.mem_range] using hdmem
      let e := j-d
      by_cases hd0 : d=0
      · subst d
        have hcj : c j=0 := by
          have ha := hanti 0 (Nat.zero_le j)
          simpa [hc0] using ha
        simp [f,hc0,hcj]
      by_cases he0 : e=0
      · have hce : c e=0 := by simpa [he0] using hc0
        have hcd : c d=0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl,hce] at ha
          omega
        simp [f,hcd,hce,e]
      by_cases hde : d=e
      · have hcd : c d=0 := by
          have ha := hanti d hdj
          rw [show j-d=e from rfl,←hde] at ha
          omega
        have hflip : j-d=d := by simpa [e] using hde.symm
        simp [f,hcd,hflip]
      · have hdpos : 0<d := Nat.pos_of_ne_zero hd0
        have hepos : 0<e := Nat.pos_of_ne_zero he0
        have hsumde : d+e=j := by dsimp [e]; omega
        have hdiv := paired_shifted_choose_term_dvd_total hp hp5 hprod hdpos hepos hde
          (show d+e ≤ B+Y by omega)
        rw [hsumde] at hdiv
        have hdiv' : ((p : ℤ)^(L+3)) ∣
            c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ)-chooseSub (B+Y-j) B e)) := by
          convert dvd_mul_of_dvd_right hdiv (c d) using 1 <;> ring
        have hz : ((c d * ((p : ℤ)^j * ((B+Y).choose j : ℤ) *
              ((chooseSub (B+Y-j) B d : ℤ)-chooseSub (B+Y-j) B e)) : ℤ) : ZMod M)=0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          simpa [M] using hdiv'
        have ha := hanti d hdj
        change f d+f e=0
        dsimp [f]
        rw [ha,←Int.cast_add]
        convert hz using 1 <;> ring
    · intro d hdmem hfd
      have hdj : d≤j := by simpa [Finset.mem_range] using hdmem
      intro heq
      have hc : c d=0 := by
        have ha := hanti d hdj
        rw [heq] at ha
        omega
      simp [f,hc] at hfd
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
    · intro d hdmem
      simp only [Finset.mem_range] at hdmem ⊢
      omega
  have hz : (((∑ d ∈ Finset.range (j+1),
      (p : ℤ)^j*c d*((B+Y).choose j : ℤ)*(chooseSub (B+Y-j) B d : ℤ)) : ℤ) : ZMod M)=0 := by
    simpa [f] using hsum
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  simpa [M] using hz
