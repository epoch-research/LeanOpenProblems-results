def E(n, f):
    val_9n_1 = 9*n + 1
    val_2n_1 = 2*n + 1
    val_1_5n_1 = 1.5*n + 1
    val_4_5n_1 = 4.5*n + 1
    val_4n_1 = 4*n + 1
    val_3n_1 = 3*n + 1
    val_n_1 = n + 1
    
    return (f.get(val_9n_1, 0) + f.get(val_2n_1, 0) + f.get(val_1_5n_1, 0) 
            - f.get(val_4_5n_1, 0) - f.get(val_4n_1, 0) - f.get(val_3n_1, 0) - f.get(val_n_1, 0))

f = {2.5: 1, 47.5: 1, 56.5: 1, 155.5: 1, 218.5: 1, 281.5: 1, 350.5: 1, 464.5: 1, 524.5: 1, 542.5: 1}

vals = set()
for n in range(601):
    vals.add(E(n, f))
print(vals)
