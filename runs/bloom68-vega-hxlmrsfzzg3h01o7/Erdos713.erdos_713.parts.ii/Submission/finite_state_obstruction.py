#!/usr/bin/env python3
"""Exact finite-state biclique certificates, not a Turan counterexample.

Run --self-test for exhaustive small-automaton checks, or --inspect FILE --t 4.
FILE is JSON with s,a,b,start,accept,delta; delta[q][a_letter*b+b_letter]
is the next state. Vertices of G_k are disjoint tagged copies of all length-k
words over the two alphabets. Edges are accepted zipped pairs, with no induced,
ordered, coloured, or homomorphism-only exclusion.

The absence of a certificate is NOT a certificate of H-freeness. It certifies
only the component condition used in the polynomial-times-vertex edge bound.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from itertools import product
import json
from math import comb
from pathlib import Path
import random

PairWord = tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class Machine:
    s: int
    a: int
    b: int
    start: int
    accept: frozenset[int]
    delta: tuple[tuple[int, ...], ...]

    @staticmethod
    def from_dict(d):
        m = Machine(d['s'], d['a'], d['b'], d['start'],
                    frozenset(d['accept']), tuple(map(tuple, d['delta'])))
        assert m.s >= 1 and m.a >= 1 and m.b >= 1
        assert 0 <= m.start < m.s and m.accept <= set(range(m.s))
        assert len(m.delta) == m.s
        assert all(len(row) == m.a*m.b for row in m.delta)
        assert all(0 <= q < m.s for row in m.delta for q in row)
        return m

    def step(self, q, x, y):
        return self.delta[q][x*self.b+y]

    def labels(self):
        return product(range(self.a), range(self.b))

    def run(self, word: PairWord, start=None):
        q = self.start if start is None else start
        for x, y in word:
            q = self.step(q, x, y)
        return q

    def accepted(self, word):
        return self.run(word) in self.accept

    def path(self, start, targets, allowed=None):
        """Shortest ordinary directed path, returned as a paired word."""
        allowed = set(range(self.s)) if allowed is None else set(allowed)
        if start not in allowed:
            return None
        prev = {start: None}
        todo = deque([start])
        while todo:
            q = todo.popleft()
            if q in targets:
                out = []
                while prev[q] is not None:
                    p, label = prev[q]
                    out.append(label)
                    q = p
                return tuple(reversed(out))
            for x, y in self.labels():
                r = self.step(q, x, y)
                if r in allowed and r not in prev:
                    prev[r] = (q, (x, y))
                    todo.append(r)
        return None

    def components(self):
        # Exact mutual-reachability classes; deliberately simple for small DFAs.
        reach = [[self.path(p, {q}) is not None for q in range(self.s)]
                 for p in range(self.s)]
        remaining = set(range(self.s))
        components = []
        while remaining:
            p = min(remaining)
            c = frozenset(q for q in remaining if reach[p][q] and reach[q][p])
            components.append(c)
            remaining -= c
        return components

    def edge_counts(self, upto):
        counts = [0]*self.s
        counts[self.start] = 1
        result = []
        for k in range(upto+1):
            result.append(sum(counts[q] for q in self.accept))
            nxt = [0]*self.s
            for q in range(self.s):
                for r in self.delta[q]:
                    nxt[r] += counts[q]
            counts = nxt
        return result


@dataclass(frozen=True)
class Collision:
    state: int
    axis: str  # H: same right, different left. V: same left, different right.
    words: tuple[PairWord, PairWord]

    def verify(self, m):
        u, v = self.words
        assert len(u) == len(v) and len(u) > 0
        assert m.run(u, self.state) == m.run(v, self.state) == self.state
        fst = lambda w: tuple(x for x, _ in w)
        snd = lambda w: tuple(y for _, y in w)
        if self.axis == 'H':
            assert snd(u) == snd(v) and fst(u) != fst(v)
        else:
            assert self.axis == 'V'
            assert fst(u) == fst(v) and snd(u) != snd(v)
        assert len(u) <= 2*m.s*m.s-1


def find_collision(m, q0, component, axis):
    """Product-automaton BFS. A persistent bit records coordinate inequality."""
    start = (q0, q0, False)
    goal = (q0, q0, True)
    todo = deque([start])
    prev = {start: None}
    if axis == 'H':
        moves = [((x, y), (xx, y), x != xx)
                 for x in range(m.a) for xx in range(m.a) for y in range(m.b)]
    else:
        moves = [((x, y), (x, yy), y != yy)
                 for x in range(m.a) for y in range(m.b) for yy in range(m.b)]
    while todo:
        q, r, diff = state = todo.popleft()
        if state == goal:
            u, v = [], []
            while prev[state] is not None:
                old, a, b = prev[state]
                u.append(a)
                v.append(b)
                state = old
            c = Collision(q0, axis, (tuple(reversed(u)), tuple(reversed(v))))
            c.verify(m)
            return c
        for a, b, d in moves:
            qq, rr = m.step(q, *a), m.step(r, *b)
            new = (qq, rr, diff or d)
            if qq in component and rr in component and new not in prev:
                prev[new] = (state, a, b)
                todo.append(new)
    return None


@dataclass(frozen=True)
class Certificate:
    order: str
    prefix: PairWord
    connector: PairWord
    suffix: PairWord
    horizontal: Collision
    vertical: Collision

    def pair(self, left_bits, right_bits):
        hh = sum((self.horizontal.words[i] for i in left_bits), ())
        vv = sum((self.vertical.words[i] for i in right_bits), ())
        u, v = (hh, vv) if self.order == 'HV' else (vv, hh)
        return self.prefix + u + self.connector + v + self.suffix

    def verify(self, m, t):
        assert t >= 1 and self.order in ('HV', 'VH')
        self.horizontal.verify(m)
        self.vertical.verify(m)
        first, second = ((self.horizontal, self.vertical) if self.order == 'HV'
                         else (self.vertical, self.horizontal))
        assert m.run(self.prefix) == first.state
        assert m.run(self.connector, first.state) == second.state
        assert m.run(self.suffix, second.state) in m.accept
        repetitions = (t-1).bit_length()
        choices = list(product((0, 1), repeat=repetitions))[:t]
        base = (0,)*repetitions
        left = [tuple(x for x, _ in self.pair(c, base)) for c in choices]
        right = [tuple(y for _, y in self.pair(base, c)) for c in choices]
        assert len(set(left)) == len(set(right)) == t
        length = len(left[0])
        assert all(len(w) == length for w in left+right)
        for i, u in enumerate(left):
            for j, v in enumerate(right):
                pair = tuple(zip(u, v))
                assert pair == self.pair(choices[i], choices[j])
                assert m.accepted(pair)
        bound = 3*(m.s-1) + (4*m.s*m.s-2)*repetitions
        assert length <= bound
        return {'t': t, 'repetitions': repetitions, 'length': length,
                'length_bound': bound, 'left': left, 'right': right}

    def to_dict(self):
        return {'order': self.order, 'prefix': self.prefix,
                'connector': self.connector, 'suffix': self.suffix,
                'horizontal': {'state': self.horizontal.state,
                               'words': self.horizontal.words},
                'vertical': {'state': self.vertical.state,
                             'words': self.vertical.words}}


@dataclass
class Analysis:
    components: list[frozenset[int]]
    branches: list[dict[str, Collision | None]]
    certificate: Certificate | None


def analyze(m):
    components = m.components()
    branches = []
    live = {q for q in range(m.s)
            if m.path(m.start, {q}) is not None and m.path(q, m.accept) is not None}
    for c in components:
        by_axis = {}
        for axis in ('H', 'V'):
            by_axis[axis] = None
            if c <= live:
                for q in sorted(c):
                    col = find_collision(m, q, c, axis)
                    if col is not None:
                        by_axis[axis] = col
                        break
        branches.append(by_axis)
    for h in (b['H'] for b in branches if b['H']):
        for v in (b['V'] for b in branches if b['V']):
            for order, first, second in (('HV', h, v), ('VH', v, h)):
                mid = m.path(first.state, {second.state})
                if mid is not None:
                    pre = m.path(m.start, {first.state})
                    post = m.path(second.state, m.accept)
                    assert pre is not None and post is not None
                    return Analysis(components, branches,
                                    Certificate(order, pre, mid, post, h, v))
    return Analysis(components, branches, None)


@dataclass(frozen=True)
class LengthProfile:
    """Exact ultimately periodic presence profile, or an explicitly finite prefix."""
    flags: tuple[bool, ...]
    cycle_start: int | None
    nfa_states_explored: int

    def contains_at(self, k):
        if k < len(self.flags):
            return self.flags[k]
        if self.cycle_start is None:
            raise ValueError('only a finite prefix was computed, not a complete profile')
        period = len(self.flags)-self.cycle_start
        return self.flags[self.cycle_start + (k-self.cycle_start) % period]


def balanced_biclique_profile(m, t=2, limit=64):
    """The unary subset automaton for ordinary K_(t,t) at equal word lengths.

    Each edge has its own DFA state. Persistent difference bits enforce
    distinct vertices WITHIN each side; sum tags separate the sides.
    Extra edges are never tested. This is an exact ordinary-copy predicate.
    The state space is finite but grows quickly; tests here use t=2.
    """
    assert t >= 1
    pairs = list((i, j) for i in range(t) for j in range(i+1, t))
    full = (1 << len(pairs))-1
    letters = tuple((x, y) for x in product(range(m.a), repeat=t)
                    for y in product(range(m.b), repeat=t))
    increments = []
    for x, y in letters:
        dx = sum((x[i] != x[j]) << b for b, (i, j) in enumerate(pairs))
        dy = sum((y[i] != y[j]) << b for b, (i, j) in enumerate(pairs))
        increments.append((x, y, dx, dy))
    transitions = {}

    def next_states(state):
        if state in transitions:
            return transitions[state]
        qs, old_x, old_y = state
        out = set()
        for x, y, dx, dy in increments:
            new = tuple(m.step(qs[i*t+j], x[i], y[j])
                        for i in range(t) for j in range(t))
            out.add((new, old_x | dx, old_y | dy))
        transitions[state] = frozenset(out)
        return transitions[state]

    current = frozenset({((m.start,)*(t*t), 0, 0)})
    seen = {}
    flags = []
    for _ in range(limit+1):
        if current in seen:
            return LengthProfile(tuple(flags), seen[current], len(transitions))
        seen[current] = len(flags)
        flags.append(any(dx == dy == full and all(q in m.accept for q in qs)
                         for qs, dx, dy in current))
        current = frozenset(z for state in current for z in next_states(state))
    return LengthProfile(tuple(flags), None, len(transitions))


def filter_free_lengths(m, profile):
    """Product with the complement of a COMPLETE presence-length profile."""
    assert profile.cycle_start is not None
    length = len(profile.flags)
    nxt = tuple(i+1 if i+1 < length else profile.cycle_start for i in range(length))
    delta = tuple(tuple(m.step(q, x, y)*length+nxt[i] for x, y in m.labels())
                  for q in range(m.s) for i in range(length))
    accept = frozenset(q*length+i for q in m.accept for i in range(length)
                       if not profile.flags[i])
    return Machine(m.s*length, m.a, m.b, m.start*length, accept, delta)


def direct_contains_C4(m, k):
    """Independent ordinary-injective test on the actual finite bipartite graph."""
    left = tuple(product(range(m.a), repeat=k))
    right = tuple(product(range(m.b), repeat=k))
    neighborhoods = []
    for x in left:
        mask = sum(1 << j for j, y in enumerate(right)
                   if m.accepted(tuple(zip(x, y))))
        neighborhoods.append(mask)
    return any((neighborhoods[i] & neighborhoods[j]).bit_count() >= 2
               for i in range(len(left)) for j in range(i+1, len(left)))


def skeleton_bound(m, k):
    """The exact coarse bound from component crossing records."""
    p = sum(comb(k, r) * m.s**(2*r+1) * (m.a*m.b)**r
            for r in range(min(m.s-1, k)+1))
    return (m.a**k+m.b**k)*p


def skeleton_check(m, analysis, max_length):
    """Independently check the injection used in the counting argument."""
    assert analysis.certificate is None
    comp_of = {q: i for i, c in enumerate(analysis.components) for q in c}
    count = 0
    for k in range(max_length+1):
        seen = {}
        accepted = 0
        for word in product(tuple(m.labels()), repeat=k):
            if not m.accepted(word):
                continue
            accepted += 1
            q = m.start
            visited = [comp_of[q]]
            record = []
            for i, (x, y) in enumerate(word):
                r = m.step(q, x, y)
                if comp_of[q] != comp_of[r]:
                    record.append((i, q, r, x, y))
                    visited.append(comp_of[r])
                q = r
            assert len(set(visited)) == len(visited) <= m.s
            no_v = all(analysis.branches[c]['V'] is None for c in visited)
            no_h = all(analysis.branches[c]['H'] is None for c in visited)
            assert no_v or no_h
            axis = 0 if no_v else 1
            projection = tuple(pair[axis] for pair in word)
            key = (axis, tuple(record), q, projection)
            assert key not in seen or seen[key] == word
            seen[key] = word
            count += 1
        assert accepted == m.edge_counts(k)[k]
        assert accepted <= skeleton_bound(m, k)
    return count


def fixtures():
    def make(s, f, accept):
        return Machine(s, 2, 2, 0, frozenset(accept),
                       tuple(tuple(f(q, x, y) for x, y in product(range(2), repeat=2))
                             for q in range(s)))
    equality = make(2, lambda q, x, y: 1 if q == 1 or x != y else 0, {0})
    one_mismatch = make(3, lambda q, x, y: min(2, q+(x != y)), {1})
    left_choices = make(2, lambda q, x, y: 1 if q == 1 or y != 0 else 0, {0})
    separated = Machine(3, 2, 2, 0, frozenset({1}),
                        ((0, 1, 0, 2), (1, 1, 2, 2), (2, 2, 2, 2)))
    # Genuinely state-dependent relation: which pair is forbidden depends on q.
    # Three live transitions per state, so exactly 3^k accepted paired words.
    context = make(3, lambda q, x, y: 2 if q == 2 or
                   (q == 0 and x == y == 1) or (q == 1 and x == 0 and y == 1)
                   else q ^ x, {0, 1})
    return {'equality': equality, 'one_mismatch': one_mismatch,
            'left_choices': left_choices, 'separated_collisions': separated,
            'state_dependent_three_choices': context}


def self_test():
    summary = {'automata': 0, 'pumping_certificates': 0, 'no_mixed_path': 0,
               'skeleton_injection_edges_checked': 0, 'count_bounds_checked': 0}

    def check(m, depth=4):
        a = analyze(m)
        summary['automata'] += 1
        if a.certificate:
            for t in (1, 2, 3, 5):
                a.certificate.verify(m, t)
            summary['pumping_certificates'] += 1
        else:
            summary['no_mixed_path'] += 1
            summary['skeleton_injection_edges_checked'] += skeleton_check(m, a, depth)
            for k, e in enumerate(m.edge_counts(64)):
                assert e <= skeleton_bound(m, k)
                summary['count_bounds_checked'] += 1
        return a

    fs = fixtures()
    for name, m in fs.items():
        a = check(m, 6)
        if name in ('equality', 'one_mismatch', 'left_choices'):
            assert a.certificate is None
        else:
            assert a.certificate is not None
    assert fs['equality'].edge_counts(20) == [2**k for k in range(21)]
    assert fs['one_mismatch'].edge_counts(20) == [k*2**k for k in range(21)]
    assert fs['left_choices'].edge_counts(20) == [2**k for k in range(21)]
    assert fs['state_dependent_three_choices'].edge_counts(20) == [3**k for k in range(21)]

    # ALL 2-state binary paired-letter DFAs, start 0, all acceptance sets.
    for flat in product(range(2), repeat=8):
        for mask in range(4):
            check(Machine(2, 2, 2, 0, frozenset(q for q in range(2) if mask >> q & 1),
                          (flat[:4], flat[4:])))
    rng = random.Random(713)
    for _ in range(200):
        s = rng.choice((3, 4, 5))
        check(Machine(s, 2, 2, 0, frozenset(q for q in range(s) if rng.randrange(2)),
                      tuple(tuple(rng.randrange(s) for _ in range(4)) for _ in range(s))),
              depth=4)
    # Rich no-mixed-path examples: all runs move through at most d transient
    # disagreement levels. These need not be H-free, so they also test that
    # the program never confuses the no-mix criterion with freeness.
    for d in range(2, 6):
        m = Machine(d+2, 2, 2, 0, frozenset(range(d+1)),
                    tuple(tuple(min(d+1, q+(x != y))
                                for x, y in product(range(2), repeat=2))
                          for q in range(d+2)))
        aa = check(m, depth=7)
        assert aa.certificate is None
        for k, count in enumerate(m.edge_counts(32)):
            assert count == 2**k*sum(comb(k, j) for j in range(min(k, d)+1))
    profiles = {}
    for name, m in fs.items():
        profile = balanced_biclique_profile(m, t=2)
        assert profile.cycle_start is not None
        for k in range(5):
            assert profile.contains_at(k) == direct_contains_C4(m, k)
        filtered = filter_free_lengths(m, profile)
        assert analyze(filtered).certificate is None
        for k, count in enumerate(filtered.edge_counts(32)):
            assert count == (0 if profile.contains_at(k) else m.edge_counts(k)[k])
        profiles[name] = {'presence_flags': profile.flags,
                          'cycle_start': profile.cycle_start,
                          'period': len(profile.flags)-profile.cycle_start,
                          'nfa_states_explored': profile.nfa_states_explored,
                          'filtered_states': filtered.s}
    context = analyze(fs['state_dependent_three_choices']).certificate
    print(json.dumps({'status': 'PASS', **summary,
                      'state_dependent_example_K55': context.verify(
                          fs['state_dependent_three_choices'], 5),
                      'state_dependent_example_certificate': context.to_dict(),
                      'ordinary_C4_length_profiles': profiles}, indent=2))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--inspect', type=Path)
    p.add_argument('--t', type=int, default=4)
    args = p.parse_args()
    if args.self_test:
        self_test()
    elif args.inspect:
        m = Machine.from_dict(json.loads(args.inspect.read_text()))
        a = analyze(m)
        if a.certificate:
            out = {'status': 'ordinary_complete_bipartite_copy',
                   'certificate': a.certificate.to_dict(),
                   'witness': a.certificate.verify(m, args.t)}
        else:
            out = {'status': 'no_mixed_accepting_component_path',
                   'warning': 'This does NOT certify H-freeness.',
                   's': m.s, 'a': m.a, 'b': m.b,
                   'bound': 'e(G_k) <= (a^k+b^k) sum_(r=0)^(s-1) '
                            'binom(k,r) s^(2r+1) (ab)^r',
                   'first_edge_counts': m.edge_counts(12)}
        print(json.dumps(out, indent=2))
    else:
        p.error('choose --self-test or --inspect FILE')


if __name__ == '__main__':
    main()
