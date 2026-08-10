#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    int max_M = 1000000;
    char *visited = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    // Forbidden set F modulo M
    // F contains 0..84, and D (87, 90, 93, 96, 99, 102, 105, 108, 111, 114, 117, 120, 123, 126),
    // and E (88, 92, 135, 144, 153, 162, 171, 180, 189)
    int D[14] = {87, 90, 93, 96, 99, 102, 105, 108, 111, 114, 117, 120, 123, 126};
    int E[9] = {88, 92, 135, 144, 153, 162, 171, 180, 189};
    
    for (int M = 192; M <= max_M; M += 3) {
        memset(visited, 0, M);
        
        // Mark forbidden residues
        // Since F has size around 100, we can just check if any reached element is in F.
        // Or we can pre-mark visited with 2 for forbidden elements.
        for (int i = 0; i < 85; i++) {
            visited[i % M] = 2;
        }
        for (int i = 0; i < 14; i++) {
            visited[D[i] % M] = 2;
        }
        for (int i = 0; i < 9; i++) {
            visited[E[i] % M] = 2;
        }
        
        int start = 85 % M;
        if (visited[start] == 2) {
            continue; // start is forbidden
        }
        
        int head = 0, tail = 0;
        visited[start] = 1;
        queue[tail++] = start;
        
        int found_bad = 0;
        while (head < tail) {
            int curr = queue[head++];
            
            // Generate transitions under g
            // g(x) = if x%3 == 0: 2*(x/3)
            //        elif x%3 == 1: 4*(x/3)+1
            //        else: 4*(x/3)+3
            int nxt[3];
            int num_nxt = 0;
            
            // Since x = q*M + curr
            // we have 3 cases for q % 3.
            for (int q = 0; q < 3; q++) {
                long long x = (long long)q * M + curr;
                long long val;
                if (x % 3 == 0) {
                    val = 2 * (x / 3);
                } else if (x % 3 == 1) {
                    val = 4 * (x / 3) + 1;
                } else {
                    val = 4 * (x / 3) + 3;
                }
                nxt[q] = val % M;
            }
            
            for (int i = 0; i < 3; i++) {
                int img = nxt[i];
                if (visited[img] == 2) {
                    found_bad = 1;
                    goto next_M;
                }
                if (visited[img] == 0) {
                    visited[img] = 1;
                    queue[tail++] = img;
                }
            }
        }
        
        next_M:
        if (!found_bad) {
            printf("FOUND BACKWARD INVARIANT MODULO M = %d!\n", M);
            printf("Reachable residues: %d\n", tail);
            free(visited);
            free(queue);
            return 0;
        }
    }
    
    printf("No backward modular invariant found under %d.\n", max_M);
    free(visited);
    free(queue);
    return 0;
}
