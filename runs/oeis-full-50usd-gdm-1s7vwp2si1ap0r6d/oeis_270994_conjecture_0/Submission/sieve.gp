a(n) = 9454129 + 11184810 * n;
my_primes = [3, 5, 7, 13, 17, 241];

check_k(k) = {
  my(covered_rules = [], order_and_inv2 = Map());
  /* Precompute order of 2 mod p */
  for(i=1, #my_primes,
    p = my_primes[i];
    order = znorder(Mod(2, p));
    mapput(order_and_inv2, p, [order, Mod(2, p)]);
  );

  for(i=1, #my_primes,
    p = my_primes[i];
    rem = k % p;
    if (rem == 0, next);
    info = mapget(order_and_inv2, p);
    order = info[1];
    g2 = info[2];
    /* Find r */
    target = -1/Mod(rem, p);
    /* discrete log */
    r_found = -1;
    curr = Mod(1, p);
    for(r=0, order-1,
      if (curr == target, r_found = r; break);
      curr *= g2;
    );
    if (r_found != -1,
      covered_rules = concat(covered_rules, [[r_found, order]]);
    );
  );
  
  /* Check if they cover mod 24 */
  uncovered = 0;
  for(m=0, 23,
    cov = 0;
    for(j=1, #covered_rules,
      rule = covered_rules[j];
      if (m % rule[2] == rule[1], cov = 1; break);
    );
    if (!cov, uncovered = 1; break);
  );
  return(!uncovered);
}

run_search() = {
  for(n=0, 100000,
    an = a(n);
    for(d=1, 13,
      k = an + 2 * d;
      if (check_k(k),
        print("FOUND! n = ", n, " d = ", d, " k = ", k);
        return(1);
      );
    );
  );
  print("Search finished, no counterexample found.");
  return(0);
}

run_search();
quit;
