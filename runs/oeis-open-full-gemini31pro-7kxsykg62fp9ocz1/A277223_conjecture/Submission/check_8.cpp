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

int main() {
    int max_p = 20;
    __int128 p10[40];
    p10[0] = 1;
    for(int i=1; i<=30; i++) p10[i] = p10[i-1] * 10;
    
    for(int i1=0; i1<=max_p; i1++)
    for(int i2=i1; i2<=max_p; i2++)
    for(int i3=i2; i3<=max_p; i3++)
    for(int i4=i3; i4<=max_p; i4++)
    for(int i5=i4; i5<=max_p; i5++)
    for(int i6=i5; i6<=max_p; i6++)
    for(int i7=i6; i7<=max_p; i7++)
    for(int i8=i7; i8<=max_p; i8++) {
        __int128 val = p10[i1] + p10[i2] + p10[i3] + p10[i4] + p10[i5] + p10[i6] + p10[i7] + p10[i8];
        if (val % 8 == 0) {
            __int128 n = val / 8;
            int max_k = 0;
            for(int k=1; k<=150; k++) {
                if (S(k * n) == k) {
                    max_k = k;
                }
            }
            if (max_k == 8) {
                cout << "Found 8! n=" << (long long)n << "\n";
                return 0;
            }
        }
    }
    cout << "None for 8 up to 20\n";
    return 0;
}
