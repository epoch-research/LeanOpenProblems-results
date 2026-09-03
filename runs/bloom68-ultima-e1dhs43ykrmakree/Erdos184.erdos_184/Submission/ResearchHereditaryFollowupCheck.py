#!/usr/bin/env python3
"""Exact audits for ResearchHereditaryFollowup.md (standard library only).

The small instances are checked from their COMPLETE binary row spaces:
  * circuits via the dimension of the subcode supported in each word;
  * minimum and maximum exact circuit partitions by independent DP;
  * an exact fractional primal for EVERY Eulerian restriction;
  * exact hereditary lower witnesses, including witnesses inside EVERY word.
No floating-point LP, assumed circuit list, or sampled restrictions are used.
Large instances are checked by exact certificate identities, NOT enumeration.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, product
from math import comb, lcm
from pathlib import Path
import json

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def bits(w):
    while w:
        b = w & -w
        yield b.bit_length() - 1
        w ^= b


def xor_all(xs):
    w = 0
    for x in xs:
        w ^= x
    return w


def span(rows):
    ans = [0]
    for r in rows:
        ans += [w ^ r for w in ans]
    return ans


def rank(rows):
    pivots = {}
    for r in rows:
        while r:
            p = r.bit_length() - 1
            if p not in pivots:
                pivots[p] = r
                break
            r ^= pivots[p]
    return len(pivots)


def kernel_of_equations(equations, d):
    """Solutions to dot(row,x)=0, as a basis of d-bit message vectors."""
    pivots = {}
    for row in equations:
        while row:
            p = row.bit_length() - 1
            if p not in pivots:
                pivots[p] = row
                break
            row ^= pivots[p]
    ordered = sorted(pivots.items())
    answer = []
    for f in range(d):
        if f in pivots:
            continue
        x = 1 << f
        for p, row in ordered:
            if (x & row).bit_count() % 2:
                x ^= 1 << p
        answer.append(x)
    assert len(answer) == d - len(pivots)
    return answer


def null_basis(columns):
    """Kernel of a matrix presented by its integer-encoded columns."""
    pivots, answer = {}, []
    for i, col in enumerate(columns):
        mask = 1 << i
        while col:
            p = col.bit_length() - 1
            if p not in pivots:
                pivots[p] = (col, mask)
                break
            a, b = pivots[p]
            col ^= a
            mask ^= b
        if not col:
            answer.append(mask)
    return answer


def columns_of_rows(rows, m):
    return [sum(((row >> e) & 1) << j for j, row in enumerate(rows))
            for e in range(m)]


class CompleteCode:
    """Independent reconstruction; no graph/circuit classification as input."""
    def __init__(self, rows, m):
        self.d, self.m, self.E = len(rows), m, (1 << m) - 1
        assert rank(rows) == self.d
        messages = span(rows)
        self.word_set = set(messages)
        assert len(messages) == len(self.word_set) == 1 << self.d
        assert self.E in self.word_set
        self.words = sorted(messages, key=lambda w: (w.bit_count(), w))
        generator_columns = columns_of_rows(rows, m)

        # Actual rank-(m-d) binary column representation of the matroid.
        parity_rows = null_basis(generator_columns)
        self.columns = columns_of_rows(parity_rows, m)
        assert len(parity_rows) == m - self.d
        assert rank(self.columns) == m - self.d
        assert xor_all(self.columns) == 0
        assert set(span(null_basis(self.columns))) == self.word_set

        supported_bases, self.circuit_set = {}, set()
        for w in self.words:
            ker = kernel_of_equations(
                (generator_columns[e] for e in bits(self.E ^ w)), self.d)
            # A nonzero binary word is minimal iff its supported subcode has
            # dimension one. This test does not use the proposed classification.
            if len(ker) == 1:
                assert w
                self.circuit_set.add(w)
            else:
                supported_bases[w] = ker

        self.contained = {}
        self.minimum, self.maximum = {0: 0}, {0: 0}
        for w in self.words:
            if w in self.circuit_set:
                contained = (w,)
            else:
                subwords = [messages[x] for x in span(supported_bases[w])]
                assert all(v & w == v for v in subwords)
                assert 0 in subwords and w in subwords
                contained = tuple(v for v in subwords if v in self.circuit_set)
            self.contained[w] = contained
            if not w:
                assert not contained
                continue
            first = w & -w
            choices = [c for c in contained if c & first]
            assert choices
            self.minimum[w] = 1 + min(self.minimum[w ^ c] for c in choices)
            self.maximum[w] = 1 + max(self.maximum[w ^ c] for c in choices)

    def primal(self, w, weights):
        """Exact load verification, using a common denominator internally."""
        den = lcm(*(x.denominator for x in weights.values())) if weights else 1
        load = [0] * self.m
        total = 0
        for c, x in weights.items():
            assert c in self.circuit_set and c & w == c and x >= 0
            z = x.numerator * (den // x.denominator)
            total += z
            for e in bits(c):
                load[e] += z
        assert load == [den * ((w >> e) & 1) for e in range(self.m)]
        return Q(total, den)

    def direct_sum_certificate(self, w, pieces):
        """Both primal and dual: these are ALL circuits contained in w."""
        assert set(pieces) == set(self.contained[w])
        assert len(pieces) == len(set(pieces))
        assert xor_all(pieces) == w
        assert sum(c.bit_count() for c in pieces) == w.bit_count()
        anchors = [c & -c for c in pieces]
        # Prices 1 on one anchor of each piece, 0 elsewhere.
        assert all(sum(bool(c & a) for a in anchors) <= 1
                   for c in self.contained[w])
        assert self.minimum[w] == self.maximum[w] == len(pieces)
        return len(pieces)

    def minimum_partitions(self, w):
        if not w:
            yield ()
            return
        first = w & -w
        for c in self.contained[w]:
            if c & first and self.minimum[w ^ c] + 1 == self.minimum[w]:
                for rest in self.minimum_partitions(w ^ c):
                    yield (c,) + rest


class CliqueBlock:
    def __init__(self, n):
        assert n >= 6 and n % 2 == 0
        self.n = n
        self.edges = list(combinations(range(n), 2))
        self.m = len(self.edges)
        self.full = (1 << self.m) - 1
        self.stars = [self.cut(1 << v) for v in range(n)]
        self.A, self.B = self.stars[0], self.full ^ self.stars[0]
        self.kernel_rows = [self.cut(1 | (1 << i)) for i in range(1, n - 1)]
        self.kernel = set(span(self.kernel_rows))
        assert len(self.kernel) == 1 << (n - 2)
        self.labels = {}
        for s, t, u in product(range(2), range(2), self.kernel):
            w = (self.A if s else 0) ^ (self.B if t else 0) ^ u
            assert w not in self.labels
            self.labels[w] = (s, t)
        self.paircuts = [self.cut((1 << u) | (1 << v)) for u, v in self.edges]
        b = 2 * ((n // 2) // 2)  # largest even b <= n/2
        self.balanced = [self.cut(sum(1 << v for v in shore))
                         for shore in combinations(range(n), b)]
        self.a, self.U = 2 * (n - 2), b * (n - b)
        self.beta, self.alpha = Q(self.a, self.U), Q(self.m, self.m - self.a)
        assert self.beta <= 1
        assert all(c in self.kernel and c for c in self.paircuts + self.balanced)
        assert all(c.bit_count() == self.a for c in self.paircuts)
        assert all(c.bit_count() == self.U for c in self.balanced)
        for e in range(self.m):
            assert sum((c >> e) & 1 for c in self.paircuts) == self.a
            assert Q(sum((c >> e) & 1 for c in self.balanced),
                     len(self.balanced)) == Q(self.U, self.m)

    def cut(self, shore):
        return sum(1 << i for i, (u, v) in enumerate(self.edges)
                   if ((shore >> u) ^ (shore >> v)) & 1)

    def audit(self):
        code = CompleteCode(self.kernel_rows + [self.A, self.B], self.m)
        assert code.word_set == set(self.labels)
        assert code.circuit_set == code.word_set - {0, self.full}
        assert code.minimum[self.full] == code.maximum[self.full] == 2
        return {"n": self.n, "words": len(code.words),
                "circuits": len(code.circuit_set), "c_full": 2,
                "alpha_certificate": str(self.alpha), "beta": str(self.beta)}


class GraphSynchronized:
    def __init__(self, base, q, edges):
        self.base, self.q = base, q
        self.edges = list(edges)
        self.h = len(self.edges)
        self.V = (1 << q) - 1
        assert all(0 <= u < v < q for u, v in self.edges)
        assert len(set(self.edges)) == self.h
        assert len(self.components(self.V)) == 1
        assert self.h >= base.alpha  # sufficient condition for exact p=h
        self.rows = [r << (e * base.m) for e in range(self.h)
                     for r in base.kernel_rows]
        self.D = tuple(sum((base.A if v == u else base.B) << (e * base.m)
                           for e, (u, z) in enumerate(self.edges) if v in (u, z))
                       for v in range(q))
        self.rows += list(self.D)
        self.code = CompleteCode(self.rows, self.h * base.m)
        assert self.code.d == self.h * (base.n - 2) + q
        assert xor_all(self.D) == self.code.E
        assert sum(c.bit_count() for c in self.D) == self.code.m
        assert all(c in self.code.circuit_set for c in self.D)

    def components(self, vertices, allowed=None):
        if allowed is None:
            allowed = range(len(self.edges))
        adjacency = [0] * self.q
        for e in allowed:
            u, v = self.edges[e]
            if vertices >> u & 1 and vertices >> v & 1:
                adjacency[u] |= 1 << v
                adjacency[v] |= 1 << u
        answer, unseen = [], vertices
        while unseen:
            todo, part = unseen & -unseen, 0
            while todo:
                a = todo & -todo
                todo ^= a
                if part & a:
                    continue
                part |= a
                todo |= adjacency[a.bit_length() - 1] & ~part
            answer.append(part)
            unseen &= ~part
        return answer

    def state(self, w):
        base = self.base
        traces = tuple((w >> (e * base.m)) & base.full for e in range(self.h))
        x = [None] * self.q
        for (u, v), z in zip(self.edges, traces):
            for a, value in zip((u, v), base.labels[z]):
                assert x[a] is None or x[a] == value
                x[a] = value
        assert all(a is not None for a in x)
        S = sum(value << v for v, value in enumerate(x))
        P = tuple(e for e, z in enumerate(traces) if z == base.full)
        Qs = tuple(e for e, z in enumerate(traces)
                   if z and base.labels[z] == (0, 0))
        internal = [e for e, (u, v) in enumerate(self.edges)
                    if S >> u & 1 and S >> v & 1]
        J = self.components(S, [e for e in internal if e not in P])
        comps = self.components(S)
        pin = sum(any(T >> u & 1 and T >> v & 1 for T in J)
                  for e in P for u, v in [self.edges[e]])
        return S, traces, P, Qs, J, comps, pin

    def primal_weights(self, w, state):
        S, traces, P, Qs, _, comps, _ = state
        base, out = self.base, Counter()
        for e in Qs:
            out[traces[e] << (e * base.m)] += Q(1)
        for T in comps:
            active = [e for e in P if T >> self.edges[e][0] & 1]
            frozen = sum(z << (e * base.m) for e, z in enumerate(traces)
                         if e not in P and any(T >> v & 1 for v in self.edges[e]))
            mass = base.alpha if w == self.code.E else Q(1)
            coefficient = mass / (len(base.paircuts) ** len(active))
            for cuts in product(base.paircuts, repeat=len(active)):
                c = frozen | sum((base.full ^ z) << (e * base.m)
                                 for e, z in zip(active, cuts))
                out[c] += coefficient
        if w != self.code.E:
            for e in P:
                for z in base.balanced:
                    out[z << (e * base.m)] += base.beta / len(base.balanced)
        return out

    def hereditary_witnesses(self, w, state, checked):
        _, traces, P, Qs, _, comps, _ = state
        base = self.base
        qpieces = [traces[e] << (e * base.m) for e in Qs]
        localpieces = qpieces + [base.paircuts[0] << (e * base.m) for e in P]
        localword = xor_all(localpieces)
        globpieces = list(qpieces)
        for T in comps:
            c = 0
            for e, (u, v) in enumerate(self.edges):
                if T >> u & 1 or T >> v & 1:
                    z = base.full ^ base.paircuts[0] if e in P else traces[e]
                    c |= z << (e * base.m)
            globpieces.append(c)
        globword = xor_all(globpieces)
        for word, pieces, value in [(localword, localpieces, len(P) + len(Qs)),
                                    (globword, globpieces, len(comps) + len(Qs))]:
            assert word in self.code.word_set and word & w == word
            if word not in checked:
                checked[word] = self.code.direct_sum_certificate(word, pieces)
            assert checked[word] == value
        return len(Qs) + max(len(P), len(comps))

    def audit(self, label, enumerate_minima=False):
        code, base = self.code, self.base
        predicted, values, generic_values, checked_witnesses = set(), {}, {}, {}
        circuit_patterns = {}
        for w in code.words:
            st = self.state(w)
            S, traces, P, Qs, J, comps, pin = st
            is_circuit = (not S and len(Qs) == 1) or \
                         (bool(S) and not P and not Qs and len(comps) == 1)
            if is_circuit:
                predicted.add(w)
                circuit_patterns[w] = S
            assert code.minimum[w] == len(Qs) + len(J) + pin
            assert code.maximum[w] == len(Qs) + len(comps) + len(P)
            value = code.primal(w, self.primal_weights(w, st))
            generic = len(Qs) + len(comps) + base.beta * len(P)
            expected = base.alpha if w == code.E else generic
            assert value == expected
            assert value <= self.h
            values[w], generic_values[w] = value, generic
            lower = self.hereditary_witnesses(w, st, checked_witnesses)
            assert code.minimum[w] <= 2 * lower
            # Q-block circuits are forced and isolated within this restriction.
            qcircuits = {traces[e] << (e * base.m) for e in Qs}
            for c in code.contained[w]:
                for e in Qs:
                    trace = (c >> (e * base.m)) & base.full
                    assert not trace or c in qcircuits
        assert predicted == code.circuit_set
        assert code.minimum[code.E] == self.q
        assert code.maximum[code.E] == self.h + 1
        assert max(code.minimum.values()) == max(self.q, self.h)
        witness_pieces = [base.paircuts[0] << (e * base.m) for e in range(self.h)]
        witness = xor_all(witness_pieces)
        assert code.direct_sum_certificate(witness, witness_pieces) == self.h
        assert max(values.values()) == self.h
        for s in range(1 << self.q):
            w = xor_all(self.D[v] for v in bits(s))
            assert code.minimum[w] == s.bit_count()
        answer = {"label": label, "n": base.n, "q": self.q, "h": self.h,
                  "elements": code.m, "rank": code.m - code.d,
                  "dimension": code.d, "all_words": len(code.words),
                  "all_circuits": len(code.circuit_set),
                  "c_full": self.q, "maximum_full_partition": self.h + 1,
                  "exact_hereditary_p": self.h,
                  "all_restriction_primals": len(values),
                  "all_restriction_factor_two_checks": len(values),
                  "distinct_exact_subrestriction_witnesses": len(checked_witnesses)}
        if self.q == 3 and self.edges == [(0, 1), (1, 2)] and base.n % 4 == 0:
            # A sharp hereditary factor-two subfamily: full first block,
            # frozen proper 11 trace in the second block. All proper nonzero
            # subwords are circuits; the full cf needs a genuinely signed dual.
            frozen = base.full ^ base.paircuts[0]
            F = base.full | (frozen << base.m)
            subwords = {w for w in code.words if w & F == w}
            assert len(subwords) == 1 << base.n
            assert subwords - {0, F} <= code.circuit_set
            assert code.minimum[F] == 2
            gamma = Q(base.n - 1, base.U)
            primal = Counter()
            for star in base.stars:
                primal[(base.full ^ star) | (frozen << base.m)] += Q(1, base.n)
            for cut in base.balanced:
                primal[cut] += gamma / len(base.balanced)
            assert code.primal(F, primal) == 1 + gamma
            anchor = (frozen & -frozen) << base.m
            anchor_price = 1 - Q(base.m - (base.n - 1), base.U)
            assert anchor_price < 0
            for c in code.contained[F]:
                assert Q((c & base.full).bit_count(), base.U) + \
                    (anchor_price if c & anchor else 0) <= 1
            assert Q(base.m, base.U) + anchor_price == 1 + gamma
            answer["sharp_factor_two_restriction"] = {
                "elements": F.bit_count(), "all_words": len(subwords),
                "all_circuits": len(subwords) - 2, "c": 2,
                "exact_cf_and_hereditary_p": str(1 + gamma),
                "signed_dual_anchor_price": str(anchor_price)}
        if enumerate_minima:
            assert self.h == comb(self.q, 2)
            counts = Counter()
            for partition in code.minimum_partitions(code.E):
                patterns = [circuit_patterns[c] for c in partition]
                t = sum(not S for S in patterns)
                assert all(S.bit_count() in (0, 1, 2) for S in patterns)
                assert sum(S.bit_count() == 2 for S in patterns) == t
                assert sum(S.bit_count() == 1 for S in patterns) == self.q - 2 * t
                subwords = span(partition)
                mean = sum((generic_values[w] for w in subwords), Q(0)) / (1 << self.q)
                formula = Q(t, 4) + 1 - Q(1, 1 << (self.q - t)) + base.beta * self.h / 4
                assert mean == formula
                counts[t] += 1
            answer["all_minimum_partitions_by_matching_size"] = dict(sorted(counts.items()))
        return answer


def parameters(q, n):
    assert q >= 3 and n >= 8 and n % 4 == 0
    h, m = comb(q, 2), comb(n, 2)
    a, U = 2 * (n - 2), n * n // 4
    beta, alpha = Q(a, U), Q(m, m - a)
    old_bounds = [Q(0)] + [1 + beta * comb(s, 2) for s in range(1, q)] + [alpha]
    mean = sum((comb(q, s) * old_bounds[s] for s in range(q + 1)), Q(0)) / (1 << q)
    closed = (2 ** q - 2 + beta * h * (2 ** (q - 2) - 1) + alpha) / (1 << q)
    assert mean == closed
    assert 0 < beta <= 1 and 1 < alpha < 2
    assert 1 - Q(a, m) + beta * Q(U, m) == 1
    assert alpha * (1 - Q(a, m)) == 1
    return {"q": q, "n": n, "h": h, "m": m,
            "elements": h * m, "dimension": h * (n - 2) + q,
            "beta": beta, "alpha": alpha, "mean_upper": mean,
            "max_old_subunion_upper": max(old_bounds)}


def large_formula_audits():
    one = parameters(5, 64)
    assert one["mean_upper"] == Q(2394037, 1937408)
    assert Q(5, 4) - one["mean_upper"] == Q(27723, 1937408)
    assert one["elements"] == 20160 and one["dimension"] == 625
    adaptive = parameters(5, 192)
    assert adaptive["max_old_subunion_upper"] == Q(479, 384) < Q(5, 4)
    for q in range(3, 65):
        p = parameters(q, 4 * q * q)
        assert p["beta"] < Q(2, q * q)
        assert p["max_old_subunion_upper"] < 2
    all_minima = parameters(9, 256)
    bounds = [Q(t, 4) + 1 - Q(1, 1 << (9 - t)) + all_minima["beta"] * 36 / 4
              for t in range(5)]
    assert max(bounds) == Q(9207, 4096)
    assert Q(9, 4) - max(bounds) == Q(9, 4096)
    # Exact elementary exchangeable probabilities, for all relevant sizes.
    for q in range(3, 65):
        for r in range(q + 1):
            orphan = Q(comb(q - 2, r - 1), comb(q, r)) if 1 <= r <= q - 1 else Q(0)
            assert orphan == Q(r * (q - r), q * (q - 1))
            assert orphan <= Q(q, 4 * (q - 1))
    # M = two direct summands M(P3,16).  The exact class theorem gives
    # c=6 and p=4; these rational upper certificates refute the one-step bound.
    n, q, h, summands = 16, 3, 2, 2
    m, a = comb(n, 2), 2 * (n - 2)
    alpha = Q(m, m - a)
    assert alpha == Q(30, 23)
    full_upper = summands * alpha
    residual_upper = (summands - 1) * alpha + h
    assert full_upper + residual_upper == Q(136, 23) < summands * q
    assert summands * h * m == 480
    assert summands * (h * (n - 2) + q) == 62
    def printable(d):
        return {k: str(v) if isinstance(v, Q) else v for k, v in d.items()}
    return {"one_step_counterexample_certificate":
                {"summands": "two copies of M(P3,16)", "elements": 480,
                 "dimension": 62, "rank": 418, "c": 6, "p": 4,
                 "cf_upper": str(full_upper),
                 "max_circuit_complement_cf_upper": str(residual_upper),
                 "one_step_rhs_upper": str(full_upper + residual_upper)},
            "specified_minimum_half_K4_counterexample": printable(one),
            "specified_minimum_every_subunion_K4_counterexample": printable(adaptive),
            "every_minimum_half_K4_counterexample":
                {**printable(all_minima), "every_minimum_mean_upper": str(max(bounds)),
                 "strict_margin_below_c_over_4": str(Q(9, 4096))},
            "asymptotic_all_subunion_formula_checks": "3 <= q <= 64; n=4q^2; max bound <2",
            "optimized_exchangeable_asymptotic_ratio": "1/8 (proved in report)"}


def coupled_kernel_audit(base):
    """Audit the new kernel-coupling lemma by supported-subcode ranks.

    Outer K is Cut(K5)+<1>, with c=2 and exact hereditary p=5/3.
    The 2^35-word coupled code is NOT enumerated. We independently enumerate
    the complete four-word subcode of the two-colored hereditary witness,
    and certify both a three-circuit partition and a complementary circuit
    pair by nullity one. The latter proves the exact global minimum is two.
    """
    q = 5
    edges = list(combinations(range(q), 2))
    h, full_outer = len(edges), (1 << len(edges)) - 1
    stars = [sum(1 << e for e, uv in enumerate(edges) if v in uv) for v in range(q)]
    outer_rows = stars[:-1] + [full_outer]
    outer = CompleteCode(outer_rows, h)
    assert outer.circuit_set == outer.word_set - {0, full_outer}
    assert outer.minimum[full_outer] == 2
    outer_primal = {full_outer ^ a: Q(1, 3) for a in stars}
    assert outer.primal(full_outer, outer_primal) == Q(5, 3)
    assert all(Q(c.bit_count(), 6) <= 1 for c in outer.circuit_set)
    assert Q(h, 6) == Q(5, 3)  # full dual; every proper word is one circuit
    A, B = stars[0], full_outer ^ stars[0]

    def tensor(a, u):
        return sum(u << (e * base.m) for e in bits(a))

    rows = [tensor(a, u) for u in base.kernel_rows for a in outer_rows]
    D = [sum((base.A if v == a else base.B) << (e * base.m)
             for e, (a, b) in enumerate(edges) if v in (a, b)) for v in range(q)]
    rows += D
    d, m = len(rows), h * base.m
    E = (1 << m) - 1
    assert d == 35 and m == 280 and rank(rows) == d
    columns = columns_of_rows(rows, m)
    parity_rows = null_basis(columns)
    representation = columns_of_rows(parity_rows, m)
    assert rank(representation) == m - d == 245
    assert xor_all(representation) == 0
    assert all(xor_all(representation[e] for e in bits(row)) == 0 for row in rows)

    def supported_words(w):
        message_basis = kernel_of_equations((columns[e] for e in bits(E ^ w)), d)
        ground_basis = [xor_all(rows[i] for i in bits(x)) for x in message_basis]
        answer = set(span(ground_basis))
        assert all(z & w == z for z in answer)
        return answer

    def circuit(w):
        assert w and supported_words(w) == {0, w}

    for c in D:
        circuit(c)
    assert xor_all(D) == E and sum(c.bit_count() for c in D) == m
    u, v = base.kernel_rows[:2]
    assert rank([u, v]) == 2
    colored = [tensor(A, u), tensor(B, v)]
    F = xor_all(colored)
    assert supported_words(F) == {0, *colored, F}
    assert not (colored[0] & colored[1])
    for c in colored:
        circuit(c)
    anchors = [c & -c for c in colored]
    assert all(sum(bool(c & a) for a in anchors) == 1 for c in colored)
    upper_partition = [E ^ tensor(full_outer, u), tensor(A, u), tensor(B, u)]
    assert xor_all(upper_partition) == E
    assert sum(c.bit_count() for c in upper_partition) == m
    for c in upper_partition:
        circuit(c)
    # A fixed, exactly checked complementary pair proves the actual minimum
    # is two in this example (E is not a circuit, since it contains D[0]).
    two_mask = 0x75D1031A5  # row order is precisely the one defined above
    two_word = xor_all(rows[i] for i in bits(two_mask))
    circuit(two_word)
    circuit(E ^ two_word)
    assert D[0] and D[0] != E
    return {"outer_code": "Cut(K5)+<1>", "outer_all_words": len(outer.words),
            "outer_c": 2, "outer_exact_hereditary_p": "5/3",
            "coupled_n": base.n, "coupled_elements": m, "coupled_dimension": d,
            "coupled_rank": m - d, "displayed_partition_size": len(D),
            "generic_lemma_partition_size": len(upper_partition),
            "exact_c_full_from_complementary_pair": 2,
            "complementary_pair_message": hex(two_mask),
            "certified_hereditary_p_lower": len(colored),
            "complete_colored_witness_subcode_words": 4,
            "large_whole_code_enumerated": False}


def main():
    assert sha256(Path(__file__).with_name("Spec.lean").read_bytes()).hexdigest() == SPEC_SHA256
    b6, b8 = CliqueBlock(6), CliqueBlock(8)
    result = {"method": "complete binary enumeration, integer DP, exact rational primal/dual certificates",
              "protected_spec_sha256": SPEC_SHA256,
              "base_blocks": [b6.audit(), b8.audit()],
              "small_complete_audits": []}
    cases = [(b8, 3, [(0, 1), (1, 2)], "P3, main n divisible by four case", False),
             (b6, 3, [(0, 1), (0, 2), (1, 2)], "K3, n=6 variant with h>=alpha", True),
             (b6, 4, [(0, 1), (1, 2), (2, 3)], "P4, n=6 variant with h>=alpha", False)]
    for base, q, edges, label, enumerate_minima in cases:
        result["small_complete_audits"].append(
            GraphSynchronized(base, q, edges).audit(label, enumerate_minima))
        print("checked " + label, flush=True)
    result["large_certificate_identity_audits_NOT_enumerations"] = large_formula_audits()
    result["coupled_kernel_supported_subcode_audit"] = coupled_kernel_audit(b8)
    print(json.dumps(result, indent=2, sort_keys=True))
    print("ALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
