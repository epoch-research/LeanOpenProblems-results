#include <iostream>
#include <vector>

using namespace std;

int S(__int128 m) {
    int s = 0;
    while(m > 0) {
        s += (int)(m % 10);
        m /= 10;
    }
    return s;
}

void print(__int128 m) {
    if (m == 0) { cout << 0; return; }
    string s = "";
    while(m > 0) {
        s += to_string((long long)(m % 10));
        m /= 10;
    }
    for(int i=s.length()-1; i>=0; i--) cout << s[i];
}

int main() {
    int max_p = 38;
    __int128 p10[40];
    p10[0] = 1;
    for(int i=1; i<=38; i++) p10[i] = p10[i-1] * 10;
    
    long long count = 0;
    for(int i1=0; i1<=max_p; i1++)
    for(int i2=i1; i2<=max_p; i2++)
    for(int i3=i2; i3<=max_p; i3++)
    for(int i4=i3; i4<=max_p; i4++)
    for(int i5=i4; i5<=max_p; i5++)
    for(int i6=i5; i6<=max_p; i6++)
    for(int i7=i6; i7<=max_p; i7++) {
        __int128 val = p10[i1] + p10[i2] + p10[i3] + p10[i4] + p10[i5] + p10[i6] + p10[i7];
        if (val % 7 == 0) {
            __int128 n = val / 7;
            int max_k = 0;
            // The sum of digits is bounded by 9 * 40 = 360
            for(int k=1; k<=360; k++) {
                if (S(k * n) == k) {
                    max_k = k;
                }
            }
            if (max_k == 7) {
                cout << "Found!\nn=";
                print(n);
                cout << "\n7n=";
                print(val);
                cout << "\n";
                return 0;
            }
        }
    }
    cout << "None up to 38\n";
    return 0;
}
