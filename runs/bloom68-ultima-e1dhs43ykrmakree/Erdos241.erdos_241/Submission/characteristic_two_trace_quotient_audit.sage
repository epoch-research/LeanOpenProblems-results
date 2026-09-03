# Exact, deterministic diagnostics for CharacteristicTwoTraceQuotients.md.
# Run from the repository root:
#   sage Submission/characteristic_two_trace_quotient_audit.sage
# No random choices, floating-point tests, or asymptotic extrapolation.

from itertools import combinations_with_replacement
from collections import Counter
from pathlib import Path
import json


def encode(x):
    return int(x.integer_representation())


def symbolic_checks():
    R = PolynomialRing(GF(2), names=('x', 'y', 'z'))
    x, y, z = R.gens()
    a = x+y+z
    b = x*y+x*z+y*z
    c = x*y*z
    assert (x+y)*(x+z)*(y+z) == a*b+c
    numerator = (x*y*(x+z)^2*(y+z)^2
                 + x*z*(x+y)^2*(y+z)^2
                 + y*z*(x+y)^2*(x+z)^2)
    assert numerator == a^3*c+a*b*c+b^3+c^2
    T = PolynomialRing(GF(2), names=('a', 'b', 'd'))
    a, b, d = T.gens()
    c = a*b+d
    assert (a^3*c+a*b*c+b^3+c^2
            == d^2+a*(a^2+b)*d+b*(a^2+b)^2)
    return {
        'berlekamp_numerator_identity': True,
        'discriminant_product_identity': True,
        'nonsquare_double_pole_expansion_identity': True,
    }


def coordinates_over_F16(theta, field16):
    # Used only for theta generating F_4096 over its F_16 subfield.
    assert len(field16) == 16
    assert theta^4096 == theta and theta^16 != theta
    theta2 = theta^2
    coordinates = {}
    for a in field16:
        for b in field16:
            for c in field16:
                coordinates[a+b*theta+c*theta2] = (a, b, c)
    assert len(coordinates) == 4096
    return coordinates


def multiplication_data(theta, q, zeta, coordinates):
    K = theta.parent()
    R = PolynomialRing(K, 'X')
    X = R.gen()
    f = prod(X+theta^(q^i) for i in range(3))
    assert f(theta) == 0 and all(a^q == a for a in f.list())
    g = sum(coordinates[zeta][i]*X^i for i in range(3))
    assert g(theta) == zeta
    mat = matrix(K, [[((g*X^j) % f)[i] for j in range(3)]
                     for i in range(3)])
    assert mat.det() != 0
    assert mat[2, 0] != 0 or mat[2, 1] != 0
    # Check the distinct discriminant divisors exactly, not numerically.
    C = PolynomialRing(K, names=('a', 'b', 'c'))
    a, b, c = C.gens()
    u = (c+f[0], b+f[1], a+f[2])
    p = [f[i]+sum(mat[i, j]*u[j] for j in range(3))
         for i in range(3)]
    dp = p[2]*p[1]+p[0]
    dq = a*b+c
    scale = dp.monomial_coefficient(a*b)
    assert dp != scale*dq
    return R, f, g, mat


def polynomial_certificate(theta, q, h, pair, coordinates):
    left, right = pair
    K = theta.parent()
    lp = prod(theta+t for t in left)
    rp = prod(theta+t for t in right)
    zeta = lp/rp
    assert zeta != 1 and zeta^h == 1
    R, f, g, mat = multiplication_data(theta, q, zeta, coordinates)
    X = R.gen()
    P = prod(X+t for t in left)
    Q = prod(X+t for t in right)
    assert P != Q
    assert P(theta) == zeta*Q(theta)
    assert P == f+(g*(Q+f)) % f
    assert (P(theta)/Q(theta))^h == 1
    left_keys = sorted(encode((theta+t)^h) for t in left)
    right_keys = sorted(encode((theta+t)^h) for t in right)
    assert left_keys != right_keys
    return {
        'left_parameters': [encode(t) for t in left],
        'right_parameters': [encode(t) for t in right],
        'zeta': encode(zeta),
        'zeta_order': int(zeta.multiplicative_order()),
        'f_coefficients_ascending': [encode(a) for a in f.list()],
        'zeta_quadratic_coefficients_ascending': [encode(g[i]) for i in range(3)],
        'multiplication_matrix_ascending_basis':
            [[encode(mat[i, j]) for j in range(3)] for i in range(3)],
        'exact_polynomial_collision_identity': True,
        'matrix_facts_checked': True,
    }


def is_strong_b3(values, modulus):
    sums = [sum(values[i] for i in tri) % modulus
            for tri in combinations_with_replacement(range(len(values)), 3)]
    return len(sums) == len(set(sums))


def q16_exhaustive():
    q, h, M = 16, 13, 315
    K = GF(2^12, name='w')
    w = K.multiplicative_generator()
    F = sorted((x for x in K if x^16 == x), key=encode)
    S = [x for x in F if sum(x^(2^i) for i in range(4)) == 0]
    H = {w^(M*i) for i in range(h)}
    assert len(F) == 16 and len(S) == 8 and len(H) == 13
    assert H.intersection(set(F)) == {K.one()}
    logs = {}
    y = K.one()
    for j in range(4095):
        logs[y] = int(j % M)
        y *= w
    assert len(logs) == 4095 and y == 1

    # These exact transformations preserve the normalized selector and B3.
    unseen = set(K)-set(F)
    representatives = []
    while unseen:
        theta = min(unseen, key=encode)
        orbit = {theta^(2^i)+s for i in range(12) for s in S}
        assert orbit <= unseen
        unseen -= orbit
        representatives.append((theta, len(orbit)))
    assert sum(n for theta, n in representatives) == 4080

    records = []
    for theta, orbit_size in representatives:
        # Independent check of the original unquotiented Bose construction,
        # using every F_16 parameter and repeated summands.
        bose_products = [prod(theta+F[i] for i in tri)
                         for tri in combinations_with_replacement(range(q), 3)]
        assert len(bose_products) == binomial(q+2, 3)
        assert len(set(bose_products)) == len(bose_products)

        parameter_for_value = {}
        for t in S:
            parameter_for_value.setdefault(logs[theta+t], t)
        values = sorted(parameter_for_value)
        by_sum = {}
        support_masks = set()
        first = six = repeated = None
        collision_pair_count = 0
        for tri in combinations_with_replacement(range(len(values)), 3):
            residue = sum(values[i] for i in tri) % M
            for previous in by_sum.get(residue, []):
                collision_pair_count += 1
                support = set(tri+previous)
                support_masks.add(sum(1 << i for i in support))
                if first is None:
                    first = (tri, previous)
                if six is None and len(support) == 6:
                    six = (tri, previous)
                if repeated is None and (len(set(tri)) < 3 or len(set(previous)) < 3):
                    repeated = (tri, previous)
            by_sum.setdefault(residue, []).append(tri)
        assert first is not None and repeated is not None

        valid_masks = [mask for mask in range(1 << len(values))
                       if not any(mask & edge == edge for edge in support_masks)]
        maximum = max(int(mask).bit_count() for mask in valid_masks)
        top_mask = next(mask for mask in valid_masks
                        if int(mask).bit_count() == maximum)
        maximizer = [values[i] for i in range(len(values)) if top_mask >> i & 1]
        assert is_strong_b3(maximizer, M)
        assert not is_strong_b3(values, M)
        # Recheck every subset independently, including the upper bound.
        for mask in range(1 << len(values)):
            sub = [values[i] for i in range(len(values)) if mask >> i & 1]
            assert is_strong_b3(sub, M) == (mask in valid_masks)

        coordinates = coordinates_over_F16(theta, F)
        root_pair = [[parameter_for_value[values[i]] for i in tri] for tri in first]
        certificate = polynomial_certificate(theta, q, h, root_pair, coordinates)
        # At the first theta also check the matrix statements for all zeta != 1.
        if not records:
            for zeta in H-{K.one()}:
                multiplication_data(theta, q, zeta, coordinates)

        records.append({
            'theta': encode(theta),
            'orbit_size': int(orbit_size),
            'image_size': len(values),
            'quotient_logarithms': values,
            'parameters_for_logarithms': [encode(parameter_for_value[a]) for a in values],
            'collision_supports': len(support_masks),
            'collision_pairs': int(collision_pair_count),
            'first_collision_value_indices': first,
            'six_distinct_collision_value_indices': six,
            'repeated_collision_value_indices': repeated,
            'maximum_strong_B3_subset_size': int(maximum),
            'maximizer_logarithms': maximizer,
            'all_subsets_independently_rechecked': True,
            'polynomial_certificate': certificate,
        })

    image_hist = Counter()
    maximum_hist = Counter()
    for rec in records:
        image_hist[rec['image_size']] += rec['orbit_size']
        maximum_hist[rec['maximum_strong_B3_subset_size']] += rec['orbit_size']
    assert len(records) == 46
    assert dict(image_hist) == {8: 3768, 7: 288, 6: 24}
    assert dict(maximum_hist) == {6: 3000, 5: 1032, 4: 48}
    return {
        'q': int(q), 'h': int(h), 'quotient_order': int(M),
        'field_modulus': str(K.modulus()),
        'primitive_generator': encode(w),
        'trace_zero_parameters': [encode(t) for t in S],
        'normalization_covers_every_theta_L_and_c': True,
        'normalized_theta_count': 4080,
        'orbit_representatives': len(records),
        'orbit_weight_sum': sum(rec['orbit_size'] for rec in records),
        'weighted_image_size_histogram': dict(image_hist),
        'weighted_maximum_subset_size_histogram': dict(maximum_hist),
        'strong_full_images': 0,
        'global_maximum_strong_B3_subset_size': max(maximum_hist),
        'every_representative_has_repeated_summand_collision': True,
        'records': records,
    }


def q256_fixed_field_diagnostic():
    q, h = 256, 13
    M = (q^3-1)//h
    K = GF(q^3, name='w')
    w = K.multiplicative_generator()
    F = GF(q, name='z')
    embedding = Hom(F, K).list()[0]
    theta = w^4097
    assert theta^4096 == theta and theta^q != theta
    assert theta.multiplicative_order() == 4095
    F16 = sorted((embedding(t) for t in F if t^16 == t), key=encode)
    parameters = [embedding(t) for t in F if t.trace() == 1]
    assert len(parameters) == 128
    assert not set(parameters).intersection(F16)
    points = [theta+t for t in parameters]
    keys = [x^h for x in points]
    assert len(set(keys)) == len(keys)

    by_class = {}
    original_products = set()
    first = six = repeated = None
    collision_pairs = 0
    triple_count = 0
    for tri in combinations_with_replacement(range(len(parameters)), 3):
        triple_count += 1
        original = prod(points[i] for i in tri)
        assert original not in original_products
        original_products.add(original)
        quotient_key = prod(keys[i] for i in tri)
        assert original^h == quotient_key
        for previous in by_class.get(quotient_key, []):
            collision_pairs += 1
            if first is None:
                first = (tri, previous)
            if six is None and len(set(tri+previous)) == 6:
                six = (tri, previous)
            if repeated is None and (len(set(tri)) < 3 or len(set(previous)) < 3):
                repeated = (tri, previous)
        by_class.setdefault(quotient_key, []).append(tri)

    coordinates = coordinates_over_F16(theta, F16)
    witnesses = {}
    for name, pair in [('first', first), ('six_distinct', six), ('repeated', repeated)]:
        assert pair is not None
        root_pair = [[parameters[i] for i in tri] for tri in pair]
        witnesses[name] = polynomial_certificate(theta, q, h, root_pair, coordinates)
    multiplicity_histogram = dict(Counter(map(len, by_class.values())))
    assert triple_count == binomial(130, 3) == 357760
    assert len(by_class) == 314546
    assert collision_pairs == 46732
    assert max(multiplicity_histogram) == 5
    assert sum(n*m for m, n in multiplicity_histogram.items()) == triple_count
    assert sum(n*binomial(m, 2) for m, n in multiplicity_histogram.items()) == collision_pairs
    return {
        'q': int(q), 'h': int(h), 'quotient_order': int(M),
        'field_modulus': str(K.modulus()),
        'primitive_generator': encode(w),
        'theta': encode(theta),
        'theta_order': int(theta.multiplicative_order()),
        'theta_in_F4096_not_F16': True,
        'selector': 'absolute trace t = 1',
        'selector_intersection_F16_size': 0,
        'selector_size': len(parameters),
        'quotient_image_size': len(set(keys)),
        'triple_multisets_including_repeats': int(triple_count),
        'distinct_triple_product_classes': len(by_class),
        'collision_pairs': int(collision_pairs),
        'maximum_triple_product_multiplicity': max(multiplicity_histogram),
        'triple_product_multiplicity_histogram': multiplicity_histogram,
        'all_unquotiented_Bose_products_distinct': True,
        'all_quotient_products_checked_independently': True,
        'witnesses': witnesses,
    }


def main():
    result = {
        'scope': 'Exact diagnostics, not a proof or disproof of Spec.lean',
        'symbolic_checks': symbolic_checks(),
        'q16_exhaustive': q16_exhaustive(),
        'q256_fixed_field_diagnostic': q256_fixed_field_diagnostic(),
        'asymptotic_bounds_proved_in_note': {
            'index13_half_trace_cubic_ratio': str(QQ(1625)/1728),
            'index7_density_five_eighths_cubic_ratio': str(QQ(109375)/110592),
        },
    }
    destination = Path('Submission/characteristic_two_trace_quotient_results.json')
    destination.write_text(json.dumps(result, indent=2, default=int)+'\n')
    q16 = result['q16_exhaustive']
    q256 = result['q256_fixed_field_diagnostic']
    print(json.dumps({
        'symbolic_checks': result['symbolic_checks'],
        'q16_orbit_representatives': q16['orbit_representatives'],
        'q16_normalized_thetas_covered': q16['orbit_weight_sum'],
        'q16_strong_full_images': q16['strong_full_images'],
        'q16_weighted_maximum_subset_size_histogram': q16['weighted_maximum_subset_size_histogram'],
        'q256_triple_count': q256['triple_multisets_including_repeats'],
        'q256_collision_pairs': q256['collision_pairs'],
        'q256_maximum_multiplicity': q256['maximum_triple_product_multiplicity'],
        'output': str(destination),
    }, indent=2, default=int))


main()
