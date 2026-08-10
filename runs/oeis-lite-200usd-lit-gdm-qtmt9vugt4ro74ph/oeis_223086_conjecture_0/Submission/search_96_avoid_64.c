#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main() {
    int max_M = 100000;
    
    char *visited = malloc(max_M);
    int *queue = malloc(max_M * sizeof(int));
    
    for (int M = 4; M <= max_M; M += 4) {
        memset(visited, 0, M);
        int head = 0, tail = 0;
        
        int r96 = 96 % M;
        int r64 = 64 % M;
        if (r96 == r64) continue;
        
        visited[r96] = 1;
        queue[tail++] = r96;
        
        int possible = 1;
        while (head < tail) {
            int curr = queue[head++];
            
            int nxt[4];
            int num_nxt = 0;
            if (curr % 2 == 0) {
                nxt[0] = ((3 * curr) / 2) % M;
                nxt[1] = ((3 * M) / 2 + (3 * curr) / 2) % M;
                num_nxt = 2;
            } else if (curr % 4 == 1) {
                int base = (3 * curr + 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            } else {
                int base = (3 * curr - 1) / 4;
                nxt[0] = base % M;
                nxt[1] = ((3 * M) / 4 + base) % M;
                nxt[2] = ((6 * M) / 4 + base) % M;
                nxt[3] = ((9 * M) / 4 + base) % M;
                num_nxt = 4;
            }
            
            for (int i = 0; i < num_nxt; i++) {
                int val = nxt[i];
                if (val == r64) {
                    possible = 0;
                    break;
                }
                if (!visited[val]) {
                    visited[val] = 1;
                    queue[tail++] = val;
                }
            }
            if (!possible) break;
        }
        
        if (possible) {
            printf("FOUND INVARIANT MODULO M = %d!\n", M);
            printf("R size: %d\n", tail);
            free(visited);
            free(queue);
            return 0;
        }
    }
    
    printf("No invariant found.\n");
    free(visited);
    free(queue);
    return 0;
}
