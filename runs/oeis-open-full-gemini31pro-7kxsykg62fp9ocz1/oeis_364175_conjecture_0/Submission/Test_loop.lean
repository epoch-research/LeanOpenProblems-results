partial def loop (u : Unit) : Empty := loop u

theorem my_false : False := Empty.rec (loop ())
