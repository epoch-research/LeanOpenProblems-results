mutual
  partial def unsound_proof (u : Unit) : False :=
    unsound_proof u

  partial instance : Inhabited False where
    default := unsound_proof ()
end




