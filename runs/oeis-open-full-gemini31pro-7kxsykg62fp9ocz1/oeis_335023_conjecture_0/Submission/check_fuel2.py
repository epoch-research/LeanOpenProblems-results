def dc_mod_fuel(fuel, a, b):
    if fuel == 0:
        return (1, 0)
    if a + 1 == b:
        return (2, 2)
    mid = (a + b) // 2
    x1, z1 = dc_mod_fuel(fuel - 1, a, mid)
    x2, z2 = dc_mod_fuel(fuel - 1, mid, b)
    if x1 == 1 and z1 == 0: return (1, 0)
    if x2 == 1 and z2 == 0: return (1, 0)
    return (2, 2)

for f in range(20, 25):
    print(f"fuel={f} result={dc_mod_fuel(f, 0, 1194648)}")
