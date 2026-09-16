unsafe def false_val : False := false_val

@[implemented_by false_val]
def false_val_safe : False := by exact?

