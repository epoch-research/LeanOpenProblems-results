#include <algorithm>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 int N=stoi(argv[1]),cut=stoi(argv[2]); long long iters=stoll(argv[3]);
 double E=stod(argv[4]); int seed=stoi(argv[5]);
 string prefix=argv[6],out=argv[7],target=argv[8];
 mt19937 rng(seed); uniform_real_distribution<double> unif(0,1);
 vector<int>A(N,0),sel,old, R(2*N,0),delta(2*N,0),touch;
 vector<double>q(2*N),prob(N);
 ifstream qt(target);for(auto &x:q)qt>>x;for(auto&x:prob)qt>>x;
 if(cut){ifstream f(prefix);int x;while(f>>x)if(x<cut)A[x]=1;}
 double mass=0;int nc=0;for(int a=0;a<N;a++){mass+=prob[a];nc+=A[a];}
 vector<pair<double,int>> order;for(int a=cut;a<N;a++)order.push_back({-log(max(unif(rng),1e-15))/max(prob[a],1e-15),a});
 sort(order.begin(),order.end());int need=max(0,min(N-cut,(int)round(mass)-nc));for(int i=0;i<need;i++)A[order[i].second]=1;
 for(int a=0;a<N;a++)if(A[a]){old.push_back(a);if(a>=cut)sel.push_back(a);}
 for(int a:old)for(int b:old)R[a+b]++;
 auto loss=[&](int n,int r){ if(n<32)return 0.0; double z=max(abs(r-q[n])-E,0.0);return z*z;};
 double obj=0;for(int n=0;n<2*N;n++)obj+=loss(n,R[n]);
 double best=obj;
 vector<int>bestA=A;
 auto report=[&](long long k){double mx=0,rm=0;int cnt=0,nb=0;for(int n=max(32,cut);n<N;n++){double d=abs(R[n]-q[n]);mx=max(mx,d);rm+=d*d;cnt++;nb+=d>E;}cerr<<"N "<<N<<" i "<<k<<" loss "<<obj<<" best "<<best<<" max "<<mx<<" rms "<<sqrt(rm/max(cnt,1))<<" bad "<<nb<<" count "<<old.size()<<endl;};
 report(0);
 for(long long k=0;k<iters;k++){
  int ai=rng()%sel.size(),a=sel[ai],b=cut+rng()%(N-cut);if(A[b])continue;
  touch.clear();auto upd=[&](int x,int d){if(delta[x]==0)touch.push_back(x);delta[x]+=d;};
  // All negative updates precede all positive updates. Duplicates are removed.
  for(int x:old)if(x!=a)upd(a+x,-2);upd(2*a,-1);
  for(int x:old)if(x!=a)upd(b+x,2);upd(2*b,1);
  sort(touch.begin(),touch.end());touch.erase(unique(touch.begin(),touch.end()),touch.end());
  double d=0;for(int n:touch)d+=loss(n,R[n]+delta[n])-loss(n,R[n]);
  double phase=double(k%max(1LL,iters/10))/max(1LL,iters/10);
  double temp=0.02+5.0*pow(1-phase,3);
  if(d<=0||unif(rng)<exp(-d/temp)){
   for(int n:touch)R[n]+=delta[n];obj+=d;A[a]=0;A[b]=1;sel[ai]=b;
   *find(old.begin(),old.end(),a)=b;
   if(obj<best-1e-7){best=obj;bestA=A;}
  }
  for(int n:touch)delta[n]=0;
  if((k+1)%max(1LL,iters/10)==0)report(k+1);
  if(best<1e-7)break;
 }
 ofstream f(out);for(int i=0;i<N;i++)if(bestA[i])f<<i<<"\n";
 cerr<<"FINAL best "<<best<<endl;
}
