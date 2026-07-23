#!/usr/bin/env node
'use strict';

// Exact integer audit for Q664.  No floating arithmetic enters any
// divisibility, gcd, content, or support calculation.  Floating logs are
// presentation only.

const TARGETS = [321, 400, 717, 800, 11576];
const GAMMA_TARGETS = new Set([321, 400, 717, 800]);
const NMAX = Math.max(...TARGETS);
const JMAX = Math.floor((NMAX - 1) / 3) + 2;

function abs(a){ return a < 0n ? -a : a; }
function gcd(a,b){ a=abs(a); b=abs(b); while(b){ const r=a%b; a=b; b=r; } return a; }
function modPos(a,m){ let r=a%m; if(r<0n) r+=m; return r; }
function logBig(a){
  a=abs(a); if(a===0n) return -Infinity;
  const s=a.toString();
  const take=Math.min(16,s.length);
  return (s.length-take)*Math.LN10 + Math.log(Number(s.slice(0,take)));
}
function fmt(x,d=12){ return Number.isFinite(x)?x.toFixed(d):String(x); }

function sieve(n){
  const is=Array(n+1).fill(true); is[0]=is[1]=false;
  for(let p=2;p*p<=n;p++) if(is[p]) for(let k=p*p;k<=n;k+=p) is[k]=false;
  return {is,primes:Array.from({length:n+1},(_,i)=>i).filter(i=>is[i])};
}
const {primes} = sieve(2*NMAX+5000);

function binom(n,k){
  if(k<0 || k>n) return 0n;
  k=Math.min(k,n-k);
  let x=1n;
  for(let i=1;i<=k;i++) x=x*BigInt(n-k+i)/BigInt(i);
  return x;
}

// Franel numbers by their exact second-order recurrence.
const F=Array(JMAX+1).fill(0n);
F[0]=1n; if(JMAX>=1) F[1]=2n;
for(let m=1;m<JMAX;m++){
  const M=BigInt(m);
  const num=(7n*M*M+7n*M+2n)*F[m]+8n*M*M*F[m-1];
  const den=BigInt(m+1)**2n;
  if(num%den!==0n) throw new Error('Franel recurrence nonintegral at '+m);
  F[m+1]=num/den;
}

// Apéry numbers only up to the largest folded index needed.
const A=Array(JMAX+1).fill(0n);
A[0]=1n; if(JMAX>=1) A[1]=5n;
for(let m=1;m<JMAX;m++){
  const M=BigInt(m);
  const P=34n*M*M*M+51n*M*M+27n*M+5n;
  const num=P*A[m]-M*M*M*A[m-1];
  const den=BigInt(m+1)**3n;
  if(num%den!==0n) throw new Error('Apery recurrence nonintegral at '+m);
  A[m+1]=num/den;
}

function Lrow(n, upto){
  const L=Array(upto+1).fill(0n); L[0]=1n;
  for(let k=0;k<upto;k++){
    const num=L[k]*BigInt(n-k)*BigInt(n+k+1);
    const den=BigInt(k+1)**2n;
    if(num%den!==0n) throw new Error(`L recurrence nonintegral n=${n} k=${k}`);
    L[k+1]=num/den;
  }
  return L;
}

function factorSmall(x, bound){
  x=abs(x); const out=[];
  for(const p of primes){
    if(p>bound || x===1n) break;
    const P=BigInt(p); let e=0;
    while(x%P===0n){ x/=P; e++; }
    if(e) out.push([p,e]);
  }
  return {factors:out,residual:x};
}
function factorString(obj){
  const s=obj.factors.map(([p,e])=>e===1?String(p):`${p}^${e}`);
  if(obj.residual!==1n) s.push(obj.residual.toString());
  return s.length?s.join('*'):'1';
}

function coefficientContent(n,J,L,prefix){
  let g=abs(prefix[J]);
  for(let d=1;d<=n;d++){
    const imin=Math.max(0,J-d+1), imax=Math.min(J,n-d);
    if(imin>imax) continue;
    let i=imin;
    let b1=binom(i+d,i);
    let t=J-i;
    let b2=binom(d-1,t);
    let c=0n;
    for(;i<=imax;i++){
      let term=L[i+d]*b1*b2*F[i];
      if((J-i)&1) c-=term; else c+=term;
      if(i<imax){
        const num1=b1*BigInt(i+d+1), den1=BigInt(i+1);
        if(num1%den1!==0n) throw new Error('b1 recurrence');
        b1=num1/den1;
        if(t<=0) throw new Error('b2 recurrence t');
        const num2=b2*BigInt(t), den2=BigInt(d-t);
        if(num2%den2!==0n) throw new Error(`b2 recurrence d=${d} t=${t}`);
        b2=num2/den2;
        t--;
      }
    }
    g=gcd(g,c);
  }
  return g;
}

function runs(indices){
  if(!indices.length) return [];
  const out=[]; let a=indices[0],b=a;
  for(let z=1;z<indices.length;z++){
    const x=indices[z];
    if(x===b+1) b=x; else {out.push([a,b]);a=b=x;}
  }
  out.push([a,b]); return out;
}

function candidateData(n,J){
  const cand=[];
  for(const p of primes){
    if(p<=n/2) continue;
    if(p>n) break;
    const r=n-p, s=p-1-r, j=Math.min(r,s);
    if(j<0 || j>J) throw new Error(`folding range n=${n} p=${p} j=${j} J=${J}`);
    const bad=(A[j]%BigInt(p)===0n);
    cand.push({p,r,s,j,bad,direct:r<=s,reflected:s<=r});
  }
  return cand;
}

function bestOneCutoff(n,J,prefix,cand,which='all',badOnly=false){
  const mass=Array(J+1).fill(0);
  let tail=0;
  for(const x of cand){
    if(which==='direct'&&!x.direct) continue;
    if(which==='reflected'&&!x.reflected) continue;
    if(badOnly&&!x.bad) continue;
    const w=Math.log(x.p); mass[x.j]+=w; tail+=w;
  }
  let best={K:-1,cost:tail,prefix:0,tail};
  for(let K=0;K<=J;K++){
    tail-=mass[K];
    const lp=logBig(prefix[K]);
    const cost=lp+tail;
    if(cost<best.cost) best={K,cost,prefix:lp,tail};
  }
  return best;
}

function summarize(n){
  const J=Math.floor((n-1)/3);
  const L=Lrow(n, Math.max(n,J+1));
  const U=Array(J+2).fill(0n), prefix=Array(J+1).fill(0n);
  let s=0n;
  for(let k=0;k<=J+1;k++){
    U[k]=L[k]*F[k];
    if(k<=J){ s+=U[k]; prefix[k]=s; }
  }
  const cand=candidateData(n,J);
  const bad=cand.filter(x=>x.bad);
  const R=bad.reduce((z,x)=>z*BigInt(x.p),1n);
  const directBad=bad.filter(x=>x.direct);
  const reflectedBad=bad.filter(x=>x.reflected);

  const uniformAll=bestOneCutoff(n,J,prefix,cand,'all',false);
  const uniformD=bestOneCutoff(n,J,prefix,cand,'direct',false);
  const uniformR=bestOneCutoff(n,J,prefix,cand,'reflected',false);
  const oracleAll=bestOneCutoff(n,J,prefix,cand,'all',true);

  let maxBadJ=-1, oracleTermRate=0;
  for(const x of bad) if(x.j>maxBadJ) maxBadJ=x.j;
  if(maxBadJ>=0) oracleTermRate=logBig(U[maxBadJ+1])/n;

  const rec={
    n,J,bad:bad.map(x=>({p:x.p,j:x.j,branch:x.direct&&x.reflected?'both':x.direct?'D':'R'})),
    R:R.toString(),Rfactor:factorString(factorSmall(R,2*n+5000)),logR:logBig(R)/n,
    uniformAll:{K:uniformAll.K,rate:uniformAll.cost/n,prefixRate:uniformAll.prefix/n,tailRate:uniformAll.tail/n},
    uniformDirect:{K:uniformD.K,rate:uniformD.cost/n},
    uniformReflected:{K:uniformR.K,rate:uniformR.cost/n},
    oracleAll:{K:oracleAll.K,rate:oracleAll.cost/n},
    maxBadJ,oracleTermRate,
    gamma:null
  };

  if(GAMMA_TARGETS.has(n)){
    const gamma=coefficientContent(n,J,L,prefix);
    if(A[n]%gamma!==0n) throw new Error(`Gamma does not divide A_n at n=${n}`);
    const pdiv=[],udiv=[];
    for(let k=0;k<=J;k++) if(prefix[k]%gamma===0n) pdiv.push(k);
    for(let k=0;k<=J+1;k++) if(U[k]%gamma===0n) udiv.push(k);
    let suffix=J;
    while(suffix>0 && prefix[suffix-1]%gamma===0n) suffix--;
    const gf=factorSmall(gamma,Math.max(5000,3*n));
    rec.gamma={
      value:gamma.toString(),factor:factorString(gf),rate:logBig(gamma)/n,
      prefixRuns:runs(pdiv),termRuns:runs(udiv),prefixSuffixStart:suffix,
      dividesEndpointTerm:(U[J+1]%gamma===0n),
      endpointTermRate:logBig(U[J+1])/n,
      quotientA:(A[n]/gamma).toString().length
    };
  }
  return rec;
}

console.log('Q664 EXACT MULTICUTOFF AUDIT');
console.log('phi(beta)=(1+beta)log(1+beta)-(1-beta)log(1-beta)-2beta log beta+beta log 8');
console.log("phi'(beta)=log(8(1-beta^2)/beta^2)>=log 64 on 0<beta<=1/3");
for(const n of TARGETS){
  const r=summarize(n);
  console.log('RESULT '+JSON.stringify(r));
}
