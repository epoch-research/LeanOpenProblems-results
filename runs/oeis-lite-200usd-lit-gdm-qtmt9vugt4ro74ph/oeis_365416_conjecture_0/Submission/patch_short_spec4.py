def main():
    # Read generate_short_spec.py
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        text = f.read()

    # Replace the exact dvd_contradiction with exact False.elim (dvd_contradiction ...)
    text = text.replace(
        "· exact dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod)",
        "· exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))"
    )
    text = text.replace(
        "· exact dvd_contradiction_25 q hq hq5_val (Nat.dvd_of_mod_eq_zero hq25_val)",
        "· exact False.elim (dvd_contradiction_25 q hq hq5_val (Nat.dvd_of_mod_eq_zero hq25_val))"
    )
    text = text.replace(
        "· exact dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val)",
        "· exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val))"
    )
    text = text.replace(
        "· exact dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod)",
        "· exact False.elim (dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod))"
    )

    with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
        f.write(text)

if __name__ == "__main__":
    main()
