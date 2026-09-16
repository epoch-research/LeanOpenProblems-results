import subprocess

cpp = """
#include <iostream>
using namespace std;

int S(__int128 m) {
    int s = 0;
    while(m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

int main() {
    int targets[] = {7, 8, 10, 11};
    for (int t=0; t<4; t++) {
        int target = targets[t];
        // Generate lengths up to 35
        // Since the sum is small, we can generate the places where we add 1s.
        // Actually, let's just do a random search over larger spaces.
    }
    cout << "Done\\n";
    return 0;
}
"""
with open("/workspace/leanproject/Submission/search_ce2.cpp", "w") as f:
    f.write(cpp)
