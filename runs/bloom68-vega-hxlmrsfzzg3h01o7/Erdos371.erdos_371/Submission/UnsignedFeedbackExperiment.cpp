// Numerical experiments only. No asymptotic conclusion is inferred.
// Compile: g++ -O3 -std=c++17 UnsignedFeedbackExperiment.cpp -o /tmp/unsigned-feedback
// Run: /tmp/unsigned-feedback 10000 100000 1000000 10000000
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

struct Row { int p; int64_t oldS, T; long double u; };

void run(int X) {
    assert(X >= 2);
    std::vector<bool> composite(X + 2, false);
    for (int p = 2; int64_t(p)*p <= X + 1; ++p)
        if (!composite[p])
            for (int64_t j = int64_t(p)*p; j <= X + 1; j += p)
                composite[j] = true;
    std::vector<int8_t> a(X + 1, 0);
    std::vector<Row> rows;
    int64_t S = 0;
    std::array<long double,10> energy{}, harmonic{}, weighted{};
    std::array<int,10> count{};
    long double maxu = 0;
    const long double logX = std::log((long double)X);
    for (int p = 2; p <= X + 1; ++p) if (!composite[p]) {
        int64_t T = 0;
        for (int m = p; m <= X + 1; m += p) {
            if (m - 1 >= 1) T += a[m-1];
            if (m <= X) T += a[m];
        }
        long double u = (static_cast<long double>(p)*T - 2*S)/X;
        rows.push_back({p, S, T, u});
        if (p > 2) {
            int b = std::min(9, int(10*std::log((long double)p)/logX));
            energy[b] += u*u/p;
            harmonic[b] += 1.0L/p;
            ++count[b];
            maxu = std::max(maxu, std::abs(u));
        }
        for (int m = p; m <= X + 1; m += p) {
            if (m - 1 >= 1) a[m-1] = 1;
            if (m <= X) a[m] = -1;
        }
        S = S - T + ((X + 1) % p == 0);
    }
    int64_t direct = 0;
    for (int n = 1; n <= X; ++n) { assert(a[n] != 0); direct += a[n]; }
    assert(direct == S);
    long double w = 1, J = 0, signed_feedback = 0, boundary = 0;
    long double mass_odd = 0, mass_all = 0, w2 = 0;
    for (auto it = rows.rbegin(); it != rows.rend(); ++it) {
        int p = it->p;
        mass_all += 2*w/p;
        if ((X+1) % p == 0) boundary += w;
        if (p > 2) {
            J += w*it->u*it->u/p;
            mass_odd += 2*w/p;
            signed_feedback += w*it->u/p;
            int b = std::min(9, int(10*std::log((long double)p)/logX));
            weighted[b] += w*it->u*it->u/p;
        } else w2 = w;
        w *= 1 - 2.0L/p;
    }
    assert(std::abs(mass_all - 1) < 1e-10L);
    assert(std::abs(mass_odd - (1-w2)) < 1e-10L);
    assert(std::abs(boundary - X*signed_feedback - S) < 1e-6L);
    std::cout << "X=" << X << " S=" << S << " S/X=" << (long double)S/X
              << " J=" << J << " sqrt(J/2)=" << std::sqrt(J/2)
              << " max_abs_u=" << maxu << " w2=" << w2 << '\n';
    std::cout << " exponent_bin count harmonic_mass sum_u2/p weighted_sum\n";
    for (int b = 0; b < 10; ++b)
        std::cout << ' ' << b/10.0 << '-' << (b+1)/10.0 << ' ' << count[b]
                  << ' ' << harmonic[b] << ' ' << energy[b] << ' '
                  << weighted[b] << '\n';
    long double mid = 0;
    for (auto &r: rows) if (r.p > 2) {
        long double t = std::log((long double)r.p)/logX;
        if (t > 0.1L && t <= 0.9L) mid += r.u*r.u/r.p;
    }
    std::cout << " energy_(X^.1,X^.9]=" << mid << "\n\n";
}

int main(int argc, char **argv) {
    std::cout << std::setprecision(12);
    if (argc == 1) run(10000);
    else for (int i = 1; i < argc; ++i) run(std::stoi(argv[i]));
}
