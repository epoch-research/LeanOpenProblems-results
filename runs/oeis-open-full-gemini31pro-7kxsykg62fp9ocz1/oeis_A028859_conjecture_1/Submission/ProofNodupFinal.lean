import Submission.ProofNodupGen
import Mathlib

theorem map1_ends_in_1 {L : ℕ} (x : Fin L → ℕ) : map1 x (Fin.last L) = 1 := Fin.snoc_last _ _
theorem map2_ends_in_1 {L : ℕ} (x : Fin L → ℕ) : map2 x (Fin.last L) = 1 := Fin.snoc_last _ _
theorem map3_ends_in_2 {L : ℕ} (x : Fin L → ℕ) : map3 x (Fin.last (L + 1)) = 2 := Fin.snoc_last _ _
theorem map4_ends_in_2 {L : ℕ} (x : Fin L → ℕ) : map4 x (Fin.last (L + 1)) = 2 := Fin.snoc_last _ _

theorem disjoint_map12_end2 {L : ℕ} (x : Fin (L+2) → ℕ) (hx : x ∈ (gen (L+1)).map map1 ++ (gen (L+1)).map map2) (hy : x ∈ [(Fin.snoc (fun _ : Fin (L+1) => (1 : ℕ)) 2 : Fin (L+2) → ℕ)]) : False := by
  simp at hy
  rw [hy] at hx
  simp at hx
  rcases hx with ⟨a, _, ha⟩ | ⟨a, _, ha⟩
  · have h1 : map1 a (Fin.last (L+1)) = 1 := map1_ends_in_1 a
    have h2 : (Fin.snoc (fun _ : Fin (L+1) => (1 : ℕ)) 2 : Fin (L+2) → ℕ) (Fin.last (L+1)) = 2 := Fin.snoc_last _ _
    rw [ha] at h1
    rw [h1] at h2
    omega
  · have h1 : map2 a (Fin.last (L+1)) = 1 := map2_ends_in_1 a
    have h2 : (Fin.snoc (fun _ : Fin (L+1) => (1 : ℕ)) 2 : Fin (L+2) → ℕ) (Fin.last (L+1)) = 2 := Fin.snoc_last _ _
    rw [ha] at h1
    rw [h1] at h2
    omega

theorem disjoint_end1_end2_gen {L : ℕ} (x : Fin (L+3) → ℕ) 
  (h1 : x ∈ (gen (L+2)).map map1 ++ (gen (L+2)).map map2) 
  (h2 : x ∈ (gen (L+1)).map map3 ++ (gen (L+1)).map map4) : False := by
  simp at h1 h2
  rcases h1 with ⟨a, _, ha⟩ | ⟨a, _, ha⟩
  · rcases h2 with ⟨b, _, hb⟩ | ⟨b, _, hb⟩
    · rw [←ha] at hb
      have := disjoint_map1_map3 a b
      exact this hb.symm
    · rw [←ha] at hb
      have := disjoint_map1_map4 a b
      exact this hb.symm
  · rcases h2 with ⟨b, _, hb⟩ | ⟨b, _, hb⟩
    · rw [←ha] at hb
      have := disjoint_map2_map3 a b
      exact this hb.symm
    · rw [←ha] at hb
      have := disjoint_map2_map4 a b
      exact this hb.symm

theorem nodup_gen (L : ℕ) : (gen L).Nodup := by
  induction' L using Nat.strongRecOn with L ih
  rcases L with _ | _ | _ | L
  · rw [gen.eq_1]; exact List.nodup_nil
  · rw [gen.eq_2]; exact List.nodup_singleton _
  · rw [gen.eq_3]
    apply List.Nodup.append
    · apply List.Nodup.append
      · apply List.Nodup.map map1_inj
        apply ih 1 (by omega)
      · apply List.Nodup.map map2_inj
        apply ih 1 (by omega)
      · intro a ha hb
        rw [List.mem_map] at ha hb
        rcases ha with ⟨xa, hxa, ha_eq⟩
        rcases hb with ⟨xb, hxb, hb_eq⟩
        rw [←ha_eq] at hb_eq
        have v_b := gen_valid 1 xb hxb
        exact disjoint_map1_map2 xa xb (by intro i; exact (gen_valid 1 xa hxa).1 i) v_b.2 hb_eq.symm
    · apply List.nodup_singleton
    · intro a ha hb
      exact disjoint_map12_end2 a ha hb
  · have h_gen : gen (L + 3) = 
      (gen (L + 2)).map map1 ++ (gen (L + 2)).map map2 ++
      ((gen (L + 1)).map map3 ++ (gen (L + 1)).map map4) := gen.eq_4 (L + 1) (by intro h; omega)
    rw [h_gen]
    apply List.Nodup.append
    · apply List.Nodup.append
      · apply List.Nodup.map map1_inj
        apply ih (L+2) (by omega)
      · apply List.Nodup.map map2_inj
        apply ih (L+2) (by omega)
      · intro a ha hb
        rw [List.mem_map] at ha hb
        rcases ha with ⟨xa, hxa, ha_eq⟩
        rcases hb with ⟨xb, hxb, hb_eq⟩
        rw [←ha_eq] at hb_eq
        have v_b := gen_valid (L+2) xb hxb
        exact disjoint_map1_map2 xa xb (by intro i; exact (gen_valid (L+2) xa hxa).1 i) v_b.2 hb_eq.symm
    · apply List.Nodup.append
      · apply List.Nodup.map map3_inj
        apply ih (L+1) (by omega)
      · apply List.Nodup.map map4_inj
        apply ih (L+1) (by omega)
      · intro a ha hb
        rw [List.mem_map] at ha hb
        rcases ha with ⟨xa, hxa, ha_eq⟩
        rcases hb with ⟨xb, hxb, hb_eq⟩
        rw [←ha_eq] at hb_eq
        have v_b := gen_valid (L+1) xb hxb
        exact disjoint_map3_map4 xa xb (by intro i; exact (gen_valid (L+1) xb hxb).1 i) (gen_valid (L+1) xa hxa).2 hb_eq.symm
    · intro a ha hb
      exact disjoint_end1_end2_gen a ha hb
