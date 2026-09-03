#include <bits/stdc++.h>
using namespace std;
#ifdef BINARY
#include "space_data_2_11.h"
const int K=4;
#else
#include "space_data_4_7.h"
const int K=3;
#endif
int seen[M]={0}, tick=0, rows[K], piv[K];
vector<pair<int,int>> cells;
long long tested=0,good=0;
void test(){
 ++tested;++tick;
 int span[1024]={0}, ns=1, vals[1024],nv=0;
 for(int i=0;i<K;i++){
  int old=ns;
  for(int j=0;j<old;j++) vals[nv++]=logs[rows[i]^span[j]];
  for(int c=1;c<Q;c++)for(int j=0;j<old;j++)span[ns++]=times[c][rows[i]]^span[j];
 }
 for(int i=0;i<nv;i++)for(int j=i;j<nv;j++)for(int k=j;k<nv;k++){
  int s=vals[i]+vals[j]+vals[k];if(s>=M)s-=M;if(s>=M)s-=M;
  if(seen[s]==tick)return;seen[s]=tick;
 }
 ++good;
 if(good<=10){cout<<"PASS";for(int i=0;i<K;i++)cout<<' '<<rows[i];cout<<"\n";cout.flush();}
}
void fillCells(int idx){
 if(idx==(int)cells.size()){test();return;}
 auto [i,j]=cells[idx];
 for(int c=0;c<Q;c++){rows[i]^=basis[j][c];fillCells(idx+1);rows[i]^=basis[j][c];}
}
void choosePiv(int i,int low){
 if(i==K){
  cells.clear();bool used[N]={0};for(int t=0;t<K;t++)used[piv[t]]=true;
  rows[0]=1;
  for(int t=1;t<K;t++){rows[t]=basis[piv[t]][1];for(int j=piv[t]+1;j<N;j++)if(!used[j])cells.push_back({t,j});}
  fillCells(0);return;
 }
 for(int j=low;j<N-(K-i)+1;j++){piv[i]=j;choosePiv(i+1,j+1);}
}
int main(){piv[0]=0;choosePiv(1,1);cout<<"q="<<Q<<" n="<<N<<" k="<<K<<" tested="<<tested<<" B3="<<good<<"\n";}
