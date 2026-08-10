import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | A047983_count m = n}

lemma count35 : A047983_count 35 = 11 := by
  unfold A047983_count tau
  native_decide

lemma no_count11_below35 (m : ℕ) (hm : m < 35) : A047983_count m ≠ 11 := by
  interval_cases m <;> (unfold A047983_count tau; native_decide)

example : a 11 = 35 := by
  rw [a]
  rw [Nat.sInf_def (s := {m : ℕ | A047983_count m = 11})]
  · exact (@Nat.find_eq_iff 35 (fun m : ℕ => m ∈ {m : ℕ | A047983_count m = 11})
      (fun a => Classical.propDecidable (a ∈ {m : ℕ | A047983_count m = 11})) _).2
      ⟨count35, no_count11_below35⟩
  · exact ⟨35, count35⟩
