// Independent exact segmented search for hard primes p=1 (mod 24), checking
// the a=1 (axis B) criterion in the FULL range 1<=m<=(p-1)/6.
// Only for B-free primes does it test axis A via complete shift factorization.
// No floating-point or probabilistic primality testing is used.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
using U=uint64_t;
U isqrt(U n) { // exact floor(sqrt(n)), using only integer division
  U lo=0,hi=U(1)<<32;
  while(lo+1<hi){U mid=lo+(hi-lo)/2; if(mid<=n/mid)lo=mid;else hi=mid;}
  return lo;
}
struct State {U prime, next;};
struct AWitness {U k=0, q=0, b=0, t=0; explicit operator bool()const{return q!=0;}};
struct BWitness {U m=0, d=0; explicit operator bool()const{return m!=0;}};
vector<uint32_t> small_primes(U n){
  vector<uint8_t> isprime(n+1,1);
  isprime[0]=isprime[1]=0;
  for(U i=2;i*i<=n;i++)if(isprime[i])for(U j=i*i;j<=n;j+=i)isprime[j]=0;
  vector<uint32_t> res;
  for(U i=2;i<=n;i++)if(isprime[i])res.push_back(i);
  return res;
}
U inverse24(U mod){ // Extended Euclidean algorithm; mod prime >=5.
  int64_t a=mod,b=24,s=0,t=1;
  while(b){int64_t d=a/b;int64_t aa=a-d*b;a=b;b=aa;int64_t ss=s-d*t;s=t;t=ss;}
  if(a!=1)abort();
  return (s%int64_t(mod)+int64_t(mod))%mod;
}
vector<U> divs(U n,const vector<uint32_t>& primes){
  const U original=n;
  vector<U> ds={1};
  for(U r:primes){
    if(r*r>n)break;
    if(n%r)continue;
    U pw=1;unsigned e=0;
    do{n/=r;e++;}while(n%r==0);
    size_t t=ds.size();
    for(unsigned i=0;i<e;i++){pw*=r;for(size_t j=0;j<t;j++)ds.push_back(ds[j]*pw);}
  }
  if(n>1){size_t t=ds.size();for(size_t j=0;j<t;j++)ds.push_back(ds[j]*n);}
  for(U q:ds)if(original%q!=0)abort();
  return ds;
}
AWitness A(U p,const vector<uint32_t>& primes){
  for(U k=1;4*k*k+2*k-1<=p;k++){
    U n=p+k,mod=4*k;
    for(U q:divs(n,primes)){
      if(q%mod!=mod-1)continue;
      U b=(q+1)/mod,t=n/q;
      if(k!=t && k<p && t<p)return {k,q,b,t};
    }
  }
  return {};
}
BWitness B(U p){
  U bound=(p-1)/6;
  for(U m=1;m<=bound;m++){
    U h=4*m-1, r=p%h;
    if(r==h-1)return {m,m};
    U delta=h-r;
    if(delta%4==0){U d=delta/4;if(d>0&&d<m&&m%d==0)return {m,d};}
  }
  return {};
}
int main(int argc,char**argv){
  if(argc<3){cerr<<"Usage: axis_segmented START_P MAX_P [BLOCK_INDEX_LENGTH=16777216]"<<endl;return 2;}
  U minp=strtoull(argv[1],nullptr,10),maxp=strtoull(argv[2],nullptr,10),
    block=argc>=4?strtoull(argv[3],nullptr,10):16777216;
  if(maxp>1000000000000ULL || block==0){
    cerr<<"This verified implementation supports MAX_P <= 10^12 and BLOCK > 0.\n";
    return 2;
  }
  if(minp<73)minp=73;
  U start=(minp-1+23)/24,end=(maxp-1)/24;
  if(start>end)abort();
  U root=isqrt(maxp+isqrt(maxp)+1)+1;
  vector<uint32_t> primes=small_primes(root);
  vector<State> states;
  for(U r:primes){
    if(r*r>maxp)break;
    if(r<=3)continue;
    U inv=inverse24(r),res=(r-inv)%r;
    U square_start=(r*r-1+23)/24,low=max(start,square_start);
    if(res<low)res+=((low-res+r-1)/r)*r;
    states.push_back({r,res});
  }
  U npr=0,n_noB=0,n_noAB=0,idx=0,total_blocks=(end-start+block)/block;
  cerr<<"Primes used="<<states.size()<<" interval="<<minp<<".."<<maxp
      <<" blocks="<<total_blocks<<" blocksize="<<block<<"\n"<<flush;
  for(U lo=start;lo<=end;lo+=block){
    U hi=min(lo+block-1,end);
    vector<uint8_t> flags(hi-lo+1,1);
    for(State& e:states){
      U r=e.prime;
      if(r*r>24*hi+1)break;
      U j=e.next;
      for(;j<=hi;j+=r)flags[j-lo]=0;
      e.next=j; // next multiple in the progression after this block.
    }
    for(U j=lo;j<=hi;j++)if(flags[j-lo]){
      U p=24*j+1;
      npr++;
      if(!B(p)){
        n_noB++;
        AWitness aw=A(p,primes);
        if(aw){cout<<"NO_B "<<p<<" A(k,q,b,t)="<<aw.k<<","<<aw.q<<","<<aw.b<<","<<aw.t<<"\n"<<flush;}
        else{n_noAB++;cout<<"NO_A_NO_B "<<p<<"\n"<<flush;}
      }
    }
    if(++idx%100==0)cerr<<"progress: p<="<<24*hi+1<<" hard_primes="<<npr
        <<" no_B="<<n_noB<<" no_A_no_B="<<n_noAB<<"\n"<<flush;
  }
  cerr<<"COMPLETE: p in ["<<minp<<","<<maxp<<"] hard_primes="<<npr
      <<" no_B="<<n_noB<<" no_A_no_B="<<n_noAB<<"\n"<<flush;
}
