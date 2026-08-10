import FormalConjectures.Util.ProblemImports

#check Finset.Iio_eventually_nonempty
#check Finset.Iio_eventually_card_ne_zero
#check Set.Iio_eventually_ncard_ne_zero

-- Try on Fin 2: if b=0, n=0 fails; if b=1, n=1 has Iio nonempty actually {0}.
-- Fin 2 top is 1, Iio 1 nonempty, so true. Fin 1 not Nontrivial. ok.
-- On Bool with bot=false top=true, Iio true={false}, true. ok.
example : True := by
  obtain ⟨b, hb⟩ := Finset.Iio_eventually_nonempty (Fin 2)
  fin_cases b <;> simp at hb
  trivial

-- For order where top=bot? nontrivial excludes. For any nontrivial orderBot, choose b ≠ bot, then Iio n nonempty for n>=b via bot<n. theorem true, no NoMax needed.
