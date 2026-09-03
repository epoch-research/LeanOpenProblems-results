import FormalConjecturesUtil
/-! Check arithmetic assembly of row-index blocks. -/
set_option maxHeartbeats 0
theorem test_assembly (P : ℕ → Prop)
    (block_checked_0 : ∀ i : Fin 100, P (0 + i.val))
    (block_checked_1 : ∀ i : Fin 100, P (100 + i.val))
    (block_checked_2 : ∀ i : Fin 100, P (200 + i.val))
    (block_checked_3 : ∀ i : Fin 100, P (300 + i.val))
    (block_checked_4 : ∀ i : Fin 100, P (400 + i.val))
    (block_checked_5 : ∀ i : Fin 100, P (500 + i.val))
    (block_checked_6 : ∀ i : Fin 100, P (600 + i.val))
    (block_checked_7 : ∀ i : Fin 100, P (700 + i.val))
    (block_checked_8 : ∀ i : Fin 100, P (800 + i.val))
    (block_checked_9 : ∀ i : Fin 100, P (900 + i.val))
    (block_checked_10 : ∀ i : Fin 100, P (1000 + i.val))
    (block_checked_11 : ∀ i : Fin 81, P (1100 + i.val))
    (r : ℕ) (hr : r ≤ 1180) : P r := by
  by_cases h0 : r < 100
  · have he : 0 + (r - 0) = r := by omega
    simpa only [he] using block_checked_0 ⟨r - 0, by omega⟩
  by_cases h1 : r < 200
  · have he : 100 + (r - 100) = r := by omega
    simpa only [he] using block_checked_1 ⟨r - 100, by omega⟩
  by_cases h2 : r < 300
  · have he : 200 + (r - 200) = r := by omega
    simpa only [he] using block_checked_2 ⟨r - 200, by omega⟩
  by_cases h3 : r < 400
  · have he : 300 + (r - 300) = r := by omega
    simpa only [he] using block_checked_3 ⟨r - 300, by omega⟩
  by_cases h4 : r < 500
  · have he : 400 + (r - 400) = r := by omega
    simpa only [he] using block_checked_4 ⟨r - 400, by omega⟩
  by_cases h5 : r < 600
  · have he : 500 + (r - 500) = r := by omega
    simpa only [he] using block_checked_5 ⟨r - 500, by omega⟩
  by_cases h6 : r < 700
  · have he : 600 + (r - 600) = r := by omega
    simpa only [he] using block_checked_6 ⟨r - 600, by omega⟩
  by_cases h7 : r < 800
  · have he : 700 + (r - 700) = r := by omega
    simpa only [he] using block_checked_7 ⟨r - 700, by omega⟩
  by_cases h8 : r < 900
  · have he : 800 + (r - 800) = r := by omega
    simpa only [he] using block_checked_8 ⟨r - 800, by omega⟩
  by_cases h9 : r < 1000
  · have he : 900 + (r - 900) = r := by omega
    simpa only [he] using block_checked_9 ⟨r - 900, by omega⟩
  by_cases h10 : r < 1100
  · have he : 1000 + (r - 1000) = r := by omega
    simpa only [he] using block_checked_10 ⟨r - 1000, by omega⟩
  have he : 1100 + (r - 1100) = r := by omega
  simpa only [he] using block_checked_11 ⟨r - 1100, by omega⟩

