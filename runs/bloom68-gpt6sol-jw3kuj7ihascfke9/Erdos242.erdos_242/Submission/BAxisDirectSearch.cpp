// Independent B-axis-first interval scan, without editing Submission/Spec.lean.
// For p=24j+1, m=1 never works; with h=4m-1, any d|m satisfying
// h | p+4d is either d=m when p%h=h-1, or d=(h-p%h)/4<m.
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <thread>
#include <vector>
using U=std::uint64_t;
using W=unsigned __int128;
U mulmod(U a,U b,U mod){return (W(a)*b)%mod;}
U powmod(U a,U b,U mod){U y=1;while(b){if(b&1)y=mulmod(y,a,mod);a=mulmod(a,a,mod);b>>=1;}return y;}
// This test rejects ONLY composites, so its use to discard failed candidates is
// unconditionally safe. The 7 bases are in addition a known 64-bit deterministic set.
bool probable_prime(U n){
 if(n<2)return false;
 for(U q:{2ULL,3ULL,5ULL,7ULL,11ULL,13ULL,17ULL,19ULL,23ULL,29ULL,31ULL,37ULL}){
  if(n%q==0)return n==q;
 }
 U u=n-1;int s=0;while((u&1)==0){u>>=1;++s;}
 for(U a:{2ULL,325ULL,9375ULL,28178ULL,450775ULL,9780504ULL,1795265022ULL}){
  if(a%n==0)continue;
  U z=powmod(a%n,u,n);
  if(z==1||z==n-1)continue;
  int r=1;for(;r<s;r++){z=mulmod(z,z,n);if(z==n-1)break;}
  if(r==s)return false;
 }
 return true;
}
struct B{U m=0,d=0;};
B b_from(U p,U begin,U end){
 for(U m=begin;m<=end;m++){
  U h=4*m-1,r=p%h;
  if(r==h-1)return{m,m};
  if((r&3)==3){U d=m-(r+1)/4;if(m%d==0)return{m,d};}
 }
 return{};
}
struct Stats{U examined=0,prefix_survivors=0,mr_survivors=0,unresolved=0,maxm=0,maxp=0,maxd=0;};
int main(int argc,char**argv){
 if(argc!=7){std::cerr<<"Usage: b_range MIN_P MAX_P THREADS PREFIX_M SEARCH_M BLOCK_J\n";return 2;}
 U lo=strtoull(argv[1],nullptr,10),hi=strtoull(argv[2],nullptr,10);
 const U threads=strtoull(argv[3],nullptr,10),prefix=strtoull(argv[4],nullptr,10),search=strtoull(argv[5],nullptr,10),block=strtoull(argv[6],nullptr,10);
 if(lo<73)lo=73;
 if(hi>=UINT64_MAX/24||threads==0||threads>96||prefix<2||search<prefix||block==0)abort();
 const U start=(lo-1+23)/24,end=(hi-1)/24;
 if(start>end)abort();
 std::atomic<U> next{start};std::vector<Stats> all(threads);std::mutex output;
 auto f=[&](U id){
  Stats& stats=all[id];
  while(true){U j=next.fetch_add(block);if(j>end)break;
   U stop=std::min(j+block-1,end);
   for(;j<=stop;j++){
    U p=24*j+1;++stats.examined;
    B b=b_from(p,2,prefix);
    if(b.m)continue;
    ++stats.prefix_survivors;
    if(!probable_prime(p))continue;
    ++stats.mr_survivors;
    b=b_from(p,prefix+1,search);
    if(!b.m){++stats.unresolved;
      std::lock_guard<std::mutex> lock(output);
      std::cout<<"UNRESOLVED "<<p<<" B-free through m="<<search<<"\n";
    }else if(b.m>stats.maxm){stats.maxm=b.m;stats.maxp=p;stats.maxd=b.d;}
   }
  }
 };
 auto t0=std::chrono::steady_clock::now();std::vector<std::thread> workers;
 for(U id=0;id<threads;id++)workers.emplace_back(f,id);
 for(auto& t:workers)t.join();
 Stats total;
 for(const Stats& s:all){total.examined+=s.examined;total.prefix_survivors+=s.prefix_survivors;
  total.mr_survivors+=s.mr_survivors;total.unresolved+=s.unresolved;
  if(s.maxm>total.maxm){total.maxm=s.maxm;total.maxp=s.maxp;total.maxd=s.maxd;}}
 auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
 std::cerr<<"SCAN ["<<lo<<","<<hi<<"] j="<<start<<".."<<end<<" examined="<<total.examined
          <<" prefix_survivors="<<total.prefix_survivors<<" probable_prime_survivors="<<total.mr_survivors
          <<" unresolved="<<total.unresolved<<" max_min_m="<<total.maxm<<" at p="<<total.maxp<<" d="<<total.maxd
          <<" elapsed_sec="<<sec<<"\n";
 if(total.examined!=end-start+1)return 3;
 return total.unresolved?1:0;
}
