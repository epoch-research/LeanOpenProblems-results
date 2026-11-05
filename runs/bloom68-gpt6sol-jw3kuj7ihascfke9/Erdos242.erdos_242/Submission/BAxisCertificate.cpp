// B-axis decision for p=1 mod 24, including rigorous complete NO-B outcomes.
// This program makes no primality assumptions; a NO-B result is about the
// stronger B criterion alone, not about the Erdős--Straus conjecture.
// Usage: b_cert N [J=~sqrt(N)/20].  Requires N>=73, N%24==1, N<2^63.
// Checks all a=4j+3 for j<J by factoring x=(N+a)/4=x0+j and testing EVERY
// divisor t|x with t>1 and t%a=a-1; then checks all m<=M, where the first
// unexamined a is A=4J+3 and M=floor((N+A)/(4(A-1))).
// Exactness: for a B witness h=4m-1, a=(N+4d)/h=3 mod 4,
// x=(N+a)/4=ma-d, t=x/d=(m/d)*a-1. Conversely such t yields
// d=x/t, m=d*(t+1)/a, and N+4d=a*(4m-1). Since 1<=d<=m,
// N=a*(4m-1)-4d >= 4m*(a-1)-a, and (N+a)/(a-1) strictly
// decreases with a. Thus any untested a>=A must have m<=M.
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>
using U=std::uint64_t;
static U sqrt_floor(U n){
 U a=std::sqrt((long double)n);
 while(a+1<=n/(a+1))++a;
 while(a>0&&a>n/a)--a;
 return a;
}
static std::vector<std::uint32_t> primes_le(U n){
 std::vector<std::uint8_t> sieve(n+1,1);
 sieve[0]=0;
 if(n>=1)sieve[1]=0;
 for(U q=2;q<=n/q;q++)if(sieve[q])for(U t=q*q;t<=n;t+=q)sieve[t]=0;
 std::vector<std::uint32_t> primes;
 for(U q=2;q<=n;q++)if(sieve[q])primes.push_back(q);
 return primes;
}
static void success(U p,U m,U d,U a,U x,U t){
 assert(m>=1&&d>=1&&m%d==0&&m<=(p-1)/6);
 assert(a>=3&&a<p&&a%4==3);
 assert(p+4*d==a*(4*m-1));
 assert(4*x==p+a&&x==d*t&&t>1&&t%a==a-1);
 std::cout<<"B "<<p<<" m="<<m<<" d="<<d<<" a="<<a<<" x="<<x<<" t="<<t<<"\n";
}
int main(int argc,char** argv){
 if(argc<2||argc>3){std::cerr<<"Usage: b_cert P [J=~sqrt(P)/20]\n";return 2;}
 U p=strtoull(argv[1],nullptr,10);
 if(p<73||p%24!=1||p>=U(1)<<63){std::cerr<<"Require P>=73, P%24=1, P<2^63\n";return 2;}
 U J=argc==3?strtoull(argv[2],nullptr,10):sqrt_floor(p)/20;
 if(J==0)J=1;
 if(J>(p-1)/4)J=(p-1)/4;
 U x0=(p+3)/4, maxx=x0+J-1;
 auto primes=primes_le(sqrt_floor(maxx));
 std::vector<U> rem(J);
 std::vector<std::vector<std::pair<U,unsigned>>> facts(J);
 for(U j=0;j<J;j++)rem[j]=x0+j;
 for(U q:primes){
  U first=x0+(q-x0%q)%q;
  for(U x=first;x<=maxx;x+=q){
   U j=x-x0;
   unsigned exponent=0;
   while(rem[j]%q==0){++exponent;rem[j]/=q;}
   if(exponent)facts[j].emplace_back(q,exponent);
  }
 }
 for(U j=0;j<J;j++){
  U a=4*j+3,x=x0+j;
  if(rem[j]>1)facts[j].emplace_back(rem[j],1);
  std::vector<U> ds={1};
  for(auto [q,e]:facts[j]){
   U pw=1,base=ds.size();
   for(unsigned h=0;h<e;h++){
    pw*=q;
    for(U i=0;i<base;i++)ds.push_back(ds[i]*pw);
   }
  }
  for(U t:ds){
   assert(x%t==0);
   if(t>1&&t%a==a-1){
    U d=x/t,m=d*((t+1)/a);
    success(p,m,d,a,x,t);
    return 0;
   }
  }
 }
 U A=4*J+3;
 U M=(static_cast<unsigned __int128>(p)+A)/
     (static_cast<unsigned __int128>(4)*(A-1));
 for(U m=1;m<=M;m++){
  U h=4*m-1,r=p%h;
  if(r==h-1){U d=m,a=(p+4*d)/h,x=(p+a)/4,t=x/d;
   success(p,m,d,a,x,t);return 0;}
  if((r&3)==3){U d=m-(r+1)/4;
   if(m%d==0){U a=(p+4*d)/h,x=(p+a)/4,t=x/d;
    success(p,m,d,a,x,t);return 0;}
  }
 }
 std::cout<<"NO_B "<<p<<" all a in {3,7,...,"<<4*(J-1)+3<<"} checked; "
          <<"remaining a >= "<<A<<" forces m <= "<<M<<", also checked.\n";
}
