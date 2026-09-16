#include <iostream>
using namespace std;

int S(__int128 m) {
    int s = 0;
    while (m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

void print(__int128 m) {
    if (m == 0) { cout << 0; return; }
    string s = "";
    while (m > 0) { s += to_string((long long)(m % 10)); m /= 10; }
    for(int i=s.length()-1; i>=0; i--) cout << s[i];
}

#include <vector>
#include <cstdlib>

int main() {
    srand(1234567);
    for (int iter = 0; iter < 10000000; iter++) {
        __int128 n = 0;
        int rem = 10;
        int length = rand() % 35 + 2;
        __int128 p10 = 1;
        for (int i = 0; i < length; i++) {
            if (rem == 0) break;
            int max_d = min(9, rem);
            int d = rand() % (max_d + 1);
            // force last digit to consume all if possible
            if (i == length - 1) {
                if (rem > 9) break; // invalid
                d = rem;
            }
            n += d * p10;
            rem -= d;
            p10 *= 10;
        }
        if (rem > 0) continue;
        
        int max_k = 0;
        for (int k = 11; k <= 300; k++) {
            if (S(k * n) == k) {
                max_k = k;
                break;
            }
        }
        if (max_k == 0) {
            cout << "FOUND! n=";
            print(n);
            cout << "\n";
            return 0;
        }
    }
    cout << "None found in 10M iterations.\n";
    return 0;
}
