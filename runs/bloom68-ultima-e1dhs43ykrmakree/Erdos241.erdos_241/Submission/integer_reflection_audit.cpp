// Exact audit of U union (V+t), with Bose log input.
// Build: g++ -O3 -std=c++17 Submission/integer_reflection_audit.cpp -o /tmp/reflection_audit
// Input: number_of_cases, then for each case q, M, and q Bose exponents in [0,M).
// Output: JSONL. Searches ALL translations having integer span <= M=q^3-1.
// Correlations use exact NTT arithmetic modulo 998244353, not floating point.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using ll = long long;
constexpr int MOD=998244353, ROOT=3;
int power(int a,int n) {
    int r=1;
    for(;n;n>>=1,a=(ll)a*a%MOD) if(n&1) r=(ll)r*a%MOD;
    return r;
}
void ntt(vector<int>& a,bool invert) {
    int n=a.size();
    for(int i=1,j=0;i<n;i++) {
        int bit=n>>1;
        for(;j&bit;bit>>=1) j^=bit;
        j^=bit;
        if(i<j) swap(a[i],a[j]);
    }
    for(int len=2;len<=n;len<<=1) {
        int wl=power(ROOT,(MOD-1)/len);
        if(invert) wl=power(wl,MOD-2);
        for(int i=0;i<n;i+=len) {
            ll w=1;
            for(int j=0;j<len/2;j++) {
                int u=a[i+j],v=w*a[i+j+len/2]%MOD;
                int x=u+v; if(x>=MOD) x-=MOD;
                int y=u-v; if(y<0) y+=MOD;
                a[i+j]=x;a[i+j+len/2]=y;w=w*wl%MOD;
            }
        }
    }
    if(invert) {
        int inv=power(n,MOD-2);
        for(auto& x:a) x=(ll)x*inv%MOD;
    }
}
int main() {
    ios::sync_with_stdio(false);cin.tie(nullptr);
    int cases;cin>>cases;
    while(cases--) {
        int q,M;cin>>q>>M;assert(M==q*q*q-1 && M%2==0);
        int m=M/2;
        vector<int>B(q),U,V,point,label;
        for(int&b:B)cin>>b;
        // Independently verify the input's cyclic strong B3 property, including repeats.
        set<int> original_sums;
        for(int i=0;i<q;i++) for(int j=i;j<q;j++) for(int k=j;k<q;k++)
            assert(original_sums.insert(((ll)B[i]+B[j]+B[k])%M).second);
        for(int b:B) {
            assert(0<=b && b<M);
            if(b%2==0)U.push_back(b/2);
            else V.push_back((M-1-b)/2);
        }
        assert(!U.empty() && !V.empty());
        for(int x:U){point.push_back(x);label.push_back(0);}
        for(int x:V){point.push_back(x);label.push_back(1);}
        auto [umin,umax]=minmax_element(U.begin(),U.end());
        auto [vmin,vmax]=minmax_element(V.begin(),V.end());
        // Span <= M iff lo <= t <= hi (the individual widths are < M).
        int lo=*umax-*vmin+1-M, hi=M-1+*umin-*vmax;
        int L=3*(m-1),n=1;
        while(n<2*L+1)n<<=1;
        assert(n<=(1<<23) && (MOD-1)%n==0);
        array<vector<int>,4>f;
        for(auto& a:f)a.assign(n,0);
        array<int,4>size{};
        for(int i=0;i<q;i++) for(int j=i;j<q;j++) for(int k=j;k<q;k++) {
            int r=label[i]+label[j]+label[k],s=point[i]+point[j]+point[k];
            assert(f[r][s]==0);f[r][s]=1;size[r]++;
        }
        for(int r=0;r<4;r++)assert(size[r]<MOD);
        for(auto& a:f)ntt(a,false);
        vector<unsigned char>bad(hi-lo+1,0);
        for(int i=0;i<4;i++)for(int j=i+1;j<4;j++) {
            vector<int> c(n);
            for(int k=0;k<n;k++)c[k]=(ll)f[i][k]*f[j][(n-k)%n]%MOD;
            ntt(c,true);
            for(int t=lo;t<=hi;t++) {
                ll lag=(ll)(j-i)*t;
                if(lag < -L || lag > L)continue;
                int idx=lag<0?lag+n:lag;
                if(c[idx]!=0)bad[t-lo]=1;
            }
        }
        // Each coefficient is at most min(|C_i|,|C_j|)<MOD, so zero is exact too.
        int count=0,best_span=M+1,best_t=0;
        for(int t=lo;t<=hi;t++) if(!bad[t-lo]) {
            count++;
            int span=max(*umax,*vmax+t)-min(*umin,*vmin+t)+1;
            if(span<best_span){best_span=span;best_t=t;}
        }
        if(count) {
            vector<int>A=U;for(int v:V)A.push_back(v+best_t);
            set<ll> sums;
            for(int i=0;i<q;i++)for(int j=i;j<q;j++)for(int k=j;k<q;k++)
                assert(sums.insert((ll)A[i]+A[j]+A[k]).second);
        }
        cout<<"{\"q\":"<<q<<",\"M\":"<<M<<",\"translation_lo\":"<<lo
            <<",\"translation_hi\":"<<hi<<",\"valid_translations\":"<<count;
        if(count)cout<<",\"best_t\":"<<best_t<<",\"best_span\":"<<best_span;
        cout<<"}\n"<<flush;
    }
}
