#!/usr/bin/env node
'use strict';

// Exact BigInt audit for Q638. No floating arithmetic enters any divisibility.
// T_n'(c)=K q_K(c) g_J(c) is used to recover all C_d efficiently.

const NMAX = Number(process.env.NMAX || 2500);
const TARGETS = (process.env.TARGETS || '321,394,717,800').split(',').map(Number);
const targetSet = new Set(TARGETS);

function abs(a){ return a<0n?-a:a; }
function gcd(a,b){ a=abs(a); b=abs(b); while(b){ const r=a%b; a=b; b=r; } return a; }
function lcm(a,b){ return a===0n||b===0n?0n:abs((a/gcd(a,b))*b); }
function modPos(a,m){ let r=a%m; if(r<0n)r+=m; return r; }
function logBig(a){ a=abs(a); if(a===0n)return -Infinity; const s=a.toString(), t=Math.min(16,s.length); return (s.length-t)*Math.LN10+Math.log(Number(s.slice(0,t))); }
function fmt(x,d=12){ return Number.isFinite(x)?x.toFixed(d):String(x); }

function sieve(n){
  const is=Array(n+1).fill(true); is[0]=is[1]=false;
  for(let p=2;p*p<=n;p++)if(is[p])for(let k=p*p;k<=n;k+=p)is[k]=false;
  return {is,primes:Array.from({length:n+1},(_,i)=>i).filter(i=>is[i])};
}
const {is:isPrime,primes}=sieve(Math.max(2*NMAX+100,2000));

function binom(n,k){
  if(k<0||k>n)return 0n; k=Math.min(k,n-k); let z=1n;
  for(let i=1;i<=k;i++)z=z*BigInt(n-k+i)/BigInt(i);
  return z;
}
function chooseRow(n){
  const a=Array(n+1).fill(0n); a[0]=1n;
  for(let k=0;k<n;k++)a[k+1]=a[k]*BigInt(n-k)/BigInt(k+1);
  return a;
}
function Lrow(n){
  const a=Array(n+1).fill(0n); a[0]=1n;
  for(let k=0;k<n;k++){
    const num=a[k]*BigInt(n-k)*BigInt(n+k+1), den=BigInt(k+1)**2n;
    if(num%den!==0n)throw new Error(`L nonintegral n=${n} k=${k}`);
    a[k+1]=num/den;
  }
  return a;
}

const JMAX=Math.floor((NMAX-1)/3)+2;
const F=Array(JMAX+1).fill(0n); F[0]=1n; if(JMAX>=1)F[1]=2n;
for(let m=1;m<JMAX;m++){
  const M=BigInt(m);
  const num=(7n*M*M+7n*M+2n)*F[m]+8n*M*M*F[m-1];
  const den=BigInt(m+1)**2n;
  if(num%den!==0n)throw new Error('Franel nonintegral '+m);
  F[m+1]=num/den;
}

const A=Array(NMAX+1).fill(0n); A[0]=1n; if(NMAX>=1)A[1]=5n;
for(let n=1;n<NMAX;n++){
  const N=BigInt(n), poly=34n*N*N*N+51n*N*N+27n*N+5n;
  const num=poly*A[n]-N*N*N*A[n-1], den=BigInt(n+1)**3n;
  if(num%den!==0n)throw new Error('Apery nonintegral '+n);
  A[n+1]=num/den;
}

function coeffData(n, full=true){
  const J=Math.floor((n-1)/3), K=J+1, L=Lrow(n), chJ=chooseRow(J);
  let C0=0n; for(let i=0;i<=J;i++)C0+=L[i]*F[i];
  const g=Array(J+1).fill(0n);
  for(let b=0;b<=J;b++)g[b]=((b&1)?-1n:1n)*chJ[b]*F[J-b];
  const q=Array(n-K+1).fill(0n);
  let ch=1n; // binom(K+a,K)
  for(let a=0;a<=n-K;a++){
    if(a>0)ch=ch*BigInt(K+a)/BigInt(a);
    q[a]=L[K+a]*ch;
  }
  let G=abs(C0), certifiedAt=0;
  const C=full?Array(n+1).fill(0n):null; if(full)C[0]=C0;
  for(let d=1;d<=n;d++){
    let s=0n;
    const amin=Math.max(0,d-1-J), amax=Math.min(n-K,d-1);
    for(let a=amin;a<=amax;a++)s+=q[a]*g[d-1-a];
    const num=BigInt(K)*s;
    if(num%BigInt(d)!==0n)throw new Error(`C division n=${n} d=${d}`);
    const cd=num/BigInt(d); if(full)C[d]=cd;
    G=gcd(G,cd);
    if(certifiedAt===0 && A[n]%G===0n)certifiedAt=d;
    if(!full && certifiedAt>0)break;
  }
  return {J,K,L,C0,C,G,certifiedAt};
}

function momentsFromC(C,eps){
  const n=C.length-1, D=Array(n+1).fill(0n);
  for(let d=0;d<=n;d++){
    let ch=1n, sign=eps===1?1n:((d&1)?-1n:1n);
    for(let k=0;k<=d;k++){
      D[k]+=sign*ch*C[d];
      if(k<d)ch=ch*BigInt(d-k)/BigInt(k+1);
    }
  }
  return D;
}

function candidateBranches(n,K){
  const rows=[];
  for(const p of primes){
    if(p<=n/2||p>n)continue;
    const r=n-p,s=p-1-r,j=Math.min(r,s);
    rows.push({p,r,s,j,direct:r<=s,reflected:s<=r,bad:A[j]%BigInt(p)===0n});
  }
  function cutoff(branch, structural){
    const arr=rows.filter(x=>x[branch] && (!structural||x.j>=2));
    return arr.length?Math.min(...arr.map(x=>x.p))-1:n;
  }
  return {rows,mD:cutoff('direct',false),mR:cutoff('reflected',false),mDs:cutoff('direct',true),mRs:cutoff('reflected',true)};
}
function core(B,D,m){ let z=abs(B); for(let k=0;k<=Math.min(m,D.length-1);k++)z=gcd(z,D[k]); return z; }

function deltaCoeffs(J){
  const c=Array(J+1).fill(0n);
  for(let k=0;k<=J;k++){
    let s=0n,ch=1n;
    for(let i=0;i<=k;i++){
      const sign=((k-i)&1)?-1n:1n;
      s+=sign*ch*A[i];
      if(i<k)ch=ch*BigInt(k-i)/BigInt(i+1);
    }
    c[k]=s;
  }
  return c;
}
function newtonValues(n,J){
  const c=deltaCoeffs(J); let U=0n,V=0n, bn=1n,bneg=1n;
  for(let k=0;k<=J;k++){
    if(k>0){ bn=bn*BigInt(n-k+1)/BigInt(k); bneg=-bneg*BigInt(n+k)/BigInt(k); }
    U+=c[k]*bn; V+=c[k]*bneg;
  }
  return {U,V,G:gcd(A[n],U*V)};
}

function trialFactor(x,limit=2000000){
  x=abs(x); const out=[];
  for(const p of primes){
    if(p>limit||BigInt(p)*BigInt(p)>x)break;
    let e=0; while(x%BigInt(p)===0n){x/=BigInt(p);e++;}
    if(e)out.push([p,e]);
  }
  if(x>1n)out.push([x.toString(),1]);
  return out;
}
function fstr(f){return f.map(([p,e])=>String(p)+(e>1?'^'+e:'')).join('*')||'1';}

let firstCounter=null,maxNeeded=0,hard=[];
for(let n=3;n<=NMAX;n++){
  const z=coeffData(n,false); maxNeeded=Math.max(maxNeeded,z.certifiedAt||n);
  if(z.certifiedAt===0){ firstCounter={n,gamma:z.G,A:A[n],ratio:A[n]%z.G}; break; }
  if(z.certifiedAt>20)hard.push([n,z.certifiedAt]);
  if(n%250===0)console.error('scan',n,'maxNeeded',maxNeeded);
}

console.log('Q638 EXACT AUDIT');
console.log('NMAX',NMAX,'firstCounter',firstCounter?JSON.stringify({n:firstCounter.n,gamma:firstCounter.gamma.toString(),rem:firstCounter.ratio.toString()}):'NONE','maxCoefficientNeeded',maxNeeded);
console.log('hardCertification',JSON.stringify(hard.slice(-30)));

for(const n of TARGETS){
  const z=coeffData(n,true), Dm=momentsFromC(z.C,-1), Dp=momentsFromC(z.C,1);
  const br=candidateBranches(n,z.K), Bm=binom(n,z.K), Bp=binom(n+z.K,z.K);
  const cores={
    Dminus:core(Bm,Dm,br.mD), Dplus:core(Bm,Dp,br.mD),
    Rminus:core(Bp,Dm,br.mR), Rplus:core(Bp,Dp,br.mR),
    DminusStruct:core(Bm,Dm,br.mDs), DplusStruct:core(Bm,Dp,br.mDs),
    RminusStruct:core(Bp,Dm,br.mRs), RplusStruct:core(Bp,Dp,br.mRs)
  };
  const nw=newtonValues(n,z.J);
  const allCore=lcm(gcd(cores.Dminus,cores.Dplus),gcd(cores.Rminus,cores.Rplus));
  const rec={
    n,J:z.J,K:z.K,certifiedAt:z.certifiedAt,
    gamma:z.G.toString(),gammaFactor:fstr(trialFactor(z.G)),gammaDivA:A[n]%z.G===0n,
    AoverGammaDigits:(A[n]/z.G).toString().length,
    newtonG:nw.G.toString(),newtonFactor:fstr(trialFactor(nw.G)),newtonOverGamma:(nw.G%z.G===0n?(nw.G/z.G).toString():'NONINTEGER'),
    newtonOverGammaFactor:(nw.G%z.G===0n?fstr(trialFactor(nw.G/z.G)):'NONINTEGER'),
    Bminus:Bm.toString(),Bplus:Bp.toString(),
    cutoffs:{mD:br.mD,mR:br.mR,mDs:br.mDs,mRs:br.mRs},
    badTop:br.rows.filter(x=>x.bad),
    cores:Object.fromEntries(Object.entries(cores).map(([k,v])=>[k,{value:v.toString(),factor:fstr(trialFactor(v)),gcdGamma:gcd(v,z.G).toString()}])),
    gammaGcdBminus:gcd(z.G,Bm).toString(),gammaGcdBplus:gcd(z.G,Bp).toString(),
    gammaGcdBoth:lcm(gcd(z.G,Bm),gcd(z.G,Bp)).toString(),
    allCore:allCore.toString(),allCoreFactor:fstr(trialFactor(allCore))
  };
  console.log('TARGET',JSON.stringify(rec));
}
