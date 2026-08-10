import Submission.Spec

noncomputable def fintype_zeros : Fintype {n : ℕ | a n = 0} :=
  Classical.choice (by infer_instance)
