// Parallel segmented B-axis arithmetic sieve for n=24j+1.
// For each (m,d) with d|m, m<=M0, mark the exact progression of j for which
// 4m-1 divides n+4d; then examine every unmarked integer by a primality
// REJECTION filter and a direct B search up to M1. Every prime passes the
// rejection filter; hence no prime with no B witness can be overlooked.
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <numeric>
#include <thread>
#include <vector>
using U=std::uint64_t;using W=unsigned __int128;
struct Class{U mod,res;};struct B{U m=0,d=0;};
U modmul(U a,U b,U m){return W(a)*b%m;}
U modpow(U a,U e,U m){U x=1;while(e){if(e&1)x=modmul(x,a,m);a=modmul(a,a,m);e>>=1;}return x;}
bool probable_prime(U n){
 if(n<2)return false;
 for(U q:{2ULL,3ULL,5ULL,7ULL,11ULL,13ULL,17ULL,19ULL,23ULL,29ULL,31ULL,37ULL})
  if(n%q==0)return n==q;
 U u=n-1;int s=0;while((u&1)==0){u>>=1;s++;}
 for(U a:{2ULL,325ULL,9375ULL,28178ULL,450775ULL,9780504ULL,1795265022ULL}){
  if(a%n==0)continue;
  U x=modpow(a%n,u,n);if(x==1||x==n-1)continue;
  int k=1;for(;k<s;k++){x=modmul(x,x,n);if(x==n-1)break;}
  if(k==s)return false;
 }
 return true;
}
U modinv(U a,U b){
 std::int64_t x0=1,x1=0,r0=a,r1=b;
 while(r1){std::int64_t q=r0/r1,t=r0-q*r1;r0=r1;r1=t;
  t=x0-q*x1;x0=x1;x1=t;}
 if(r0!=1)abort();
 return (x0%std::int64_t(b)+std::int64_t(b))%b;
}
std::vector<Class> make_classes(U limit){
 std::vector<Class> classes;
 for(U m=2;m<=limit;m++){
  U h=4*m-1,g=std::gcd(U(24),h),q=h/g,inverse=modinv(24/g,q);
  for(U d=1;d<=m;d++)if(m%d==0 && (1+4*d)%g==0){
   U v=(1+4*d)/g;
   U residue=(q-(v%q)*inverse%q)%q;
   if((24*residue+1+4*d)%h!=0)abort();
   classes.push_back({q,residue});
  }
 }
 return classes;
}
B directB(U n,U lo,U hi){
 for(U m=lo;m<=hi;m++){
  U h=4*m-1,r=n%h;
  if(r==h-1)return{m,m};
  if((r&3)==3){U d=m-(r+1)/4;if(m%d==0)return{m,d};}
 }
 return{};
}
struct Stats{U examined=0,unmarked=0,mr_survivors=0,unresolved=0,maxm=0,maxp=0,maxd=0;};
int main(int argc,char**argv){
 if(argc!=7){std::cerr<<"Usage: b_sieve MIN_P MAX_P THREADS SIEVE_M SEARCH_M BLOCK_J\n";return 2;}
 U lo=strtoull(argv[1],nullptr,10),hi=strtoull(argv[2],nullptr,10),
  nth=strtoull(argv[3],nullptr,10),M0=strtoull(argv[4],nullptr,10),M1=strtoull(argv[5],nullptr,10),
  block=strtoull(argv[6],nullptr,10);
 if(lo<73||hi>=UINT64_MAX/24||lo>hi||nth<1||nth>96||M0<2||M0>M1||block<1)abort();
 U start=(lo-1+23)/24,end=(hi-1)/24;
 if(start>end)abort();
 std::vector<Class> classes=make_classes(M0);
 std::atomic<U> next{start};std::vector<Stats> all(nth);std::mutex output;
 auto f=[&](U id){
  Stats& s=all[id];std::vector<std::uint8_t> flags;
  while(true){
   U base=next.fetch_add(block);if(base>end)break;
   U length=std::min(block,end-base+1),last=base+length-1;
   flags.assign(length,1);
   for(auto [mod,res]:classes){U first=base+(res+mod-(base%mod))%mod;
    for(U j=first;j<=last;j+=mod)flags[j-base]=0;
   }
   s.examined+=length;
   for(U k=0;k<length;k++)if(flags[k]){
    ++s.unmarked;U n=24*(base+k)+1;
    if(!probable_prime(n))continue;
    ++s.mr_survivors;
    B b=directB(n,M0+1,M1);
    if(!b.m){++s.unresolved;std::lock_guard<std::mutex> guard(output);
      std::cout<<"UNRESOLVED "<<n<<" B-free through m="<<M1<<"\n";
    }else if(b.m>s.maxm){s.maxm=b.m;s.maxp=n;s.maxd=b.d;}
   }
  }
 };
 auto t0=std::chrono::steady_clock::now();std::vector<std::thread> threads;
 for(U id=0;id<nth;id++)threads.emplace_back(f,id);
 for(auto& t:threads)t.join();
 Stats total;
 for(Stats s:all){total.examined+=s.examined;total.unmarked+=s.unmarked;
  total.mr_survivors+=s.mr_survivors;total.unresolved+=s.unresolved;
  if(s.maxm>total.maxm){total.maxm=s.maxm;total.maxp=s.maxp;total.maxd=s.maxd;}}
 auto elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();
 std::cerr<<"SEGMENTED ["<<lo<<","<<hi<<"] j="<<start<<".."<<end
   <<" classes="<<classes.size()<<" examined="<<total.examined<<" unmarked="<<total.unmarked
   <<" probable_prime_survivors="<<total.mr_survivors<<" unresolved="<<total.unresolved
   <<" max_min_m="<<total.maxm<<" at p="<<total.maxp<<" d="<<total.maxd
   <<" elapsed_sec="<<elapsed<<"\n";
 if(total.examined!=end-start+1)return 3;
 return total.unresolved?1:0;
}
