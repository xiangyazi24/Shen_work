#!/usr/bin/env node
'use strict';

// Q619 exact BigInt computation.  No floating arithmetic enters any gcd,
// residue, or factorization.  Floating logs are presentation only.

const TARGETS = [400, 600, 800];
const NMAX = Math.max(...TARGETS);
const SIEVE_MAX = 2 * NMAX + 100;

function abs(a){ return a < 0n ? -a : a; }
function gcd(a,b){ a=abs(a); b=abs(b); while(b){ const r=a%b; a=b; b=r; } return a; }
function lcm(a,b){ if(a===0n||b===0n) return 0n; return abs((a/gcd(a,b))*b); }
function modPos(a,m){ let r=a%m; if(r<0n) r+=m; return r; }
function minBig(a,b){ return a<b?a:b; }
function logBig(a){
  a=abs(a); if(a===0n) return -Infinity;
  const s=a.toString(), take=Math.min(16,s.length);
  return (s.length-take)*Math.LN10 + Math.log(Number(s.slice(0,take)));
}
function fmt(x,d=12){ return Number.isFinite(x)?x.toFixed(d):String(x); }

function sieve(n){
  const is=Array(n+1).fill(true); is[0]=is[1]=false;
  for(let p=2;p*p<=n;p++) if(is[p]) for(let k=p*p;k<=n;k+=p) is[k]=false;
  return {is,primes:Array.from({length:n+1},(_,i)=>i).filter(i=>is[i])};
}
const {primes}=sieve(SIEVE_MAX);

function binom(n,k){
  if(k<0||k>n) return 0n;
  k=Math.min(k,n-k);
  let x=1n;
  for(let i=1;i<=k;i++) x=x*BigInt(n-k+i)/BigInt(i);
  return x;
}

// Franel numbers and the c=+/-1 binomial transforms.
const JMAX=Math.floor((NMAX-1)/3)+2;
const F=Array(JMAX+1).fill(0n);
const gPlus=Array(JMAX+1).fill(0n);
const gMinus=Array(JMAX+1).fill(0n);
let pascal=[1n];
for(let m=0;m<=JMAX;m++){
  let fm=0n;
  for(const c of pascal) fm+=c*c*c;
  F[m]=fm;
  let gp=0n,gm=0n;
  for(let i=0;i<=m;i++){
    gm+=pascal[i]*F[i];
    gp+=((m-i)&1?-1n:1n)*pascal[i]*F[i];
  }
  gPlus[m]=gp; gMinus[m]=gm;
  const next=Array(m+2).fill(0n);
  for(let i=0;i<=m;i++){ next[i]+=pascal[i]; next[i+1]+=pascal[i]; }
  pascal=next;
}

// Apéry numbers for exact verification of the top-half bad support.
const Apery=Array(NMAX+1).fill(0n); Apery[0]=1n; Apery[1]=5n;
for(let n=1;n<NMAX;n++){
  const N=BigInt(n);
  const poly=34n*N*N*N+51n*N*N+27n*N+5n;
  const num=poly*Apery[n]-N*N*N*Apery[n-1];
  const den=BigInt(n+1)**3n;
  if(num%den!==0n) throw new Error('nonintegral Apéry recurrence at '+n);
  Apery[n+1]=num/den;
}

function Lrow(n){
  const L=Array(n+1).fill(0n); L[0]=1n;
  for(let k=0;k<n;k++){
    const num=L[k]*BigInt(n-k)*BigInt(n+k+1);
    const den=BigInt(k+1)*BigInt(k+1);
    if(num%den!==0n) throw new Error(`nonintegral L row n=${n} k=${k}`);
    L[k+1]=num/den;
  }
  return L;
}
function chooseRow(n){
  const a=Array(n+1).fill(0n); a[0]=1n;
  for(let k=0;k<n;k++) a[k+1]=a[k]*BigInt(n-k)/BigInt(k+1);
  return a;
}
function chooseKArray(K,maxA){
  const a=Array(maxA+1).fill(0n); a[0]=1n;
  for(let x=0;x<maxA;x++) a[x+1]=a[x]*BigInt(K+x+1)/BigInt(x+1);
  return a;
}
function centered(D0,g){
  g=abs(g); if(g===0n) return abs(D0);
  const r=modPos(D0,g);
  if(r===0n) return g; // least nonzero member of the affine lattice
  return minBig(r,g-r);
}

function candidateData(n){
  const cand=primes.filter(p=>2*p>n && p<=n);
  const rows=[];
  for(const p of cand){
    const r=n-p, s=p-1-r, j=Math.min(r,s);
    const direct=r<=s, reflected=s<=r;
    const bad=Apery[j]%BigInt(p)===0n;
    rows.push({p,r,s,j,direct,reflected,bad});
  }
  function least(pred){ const a=rows.filter(pred).map(x=>x.p); return a.length?Math.min(...a):Infinity; }
  return {
    rows,
    pAll:least(()=>true),
    pDirect:least(x=>x.direct),
    pReflected:least(x=>x.reflected),
    pDirectStruct:least(x=>x.direct&&x.j>=2),
    pReflectedStruct:least(x=>x.reflected&&x.j>=2)
  };
}
function safeM(p,n){ return Number.isFinite(p)?Math.min(n,p-1):n; }

function momentsMinus(n,L,J,K,thresholds){
  const maxm=Math.max(...Object.values(thresholds));
  const chJ=chooseRow(J), chK=chooseKArray(K,maxm);
  let D0=0n;
  for(let u=0;u<=J;u++) D0+=(((n+u)&1)?-1n:1n)*L[u]*gMinus[u];
  let g=0n;
  const out={D0,at:{}};
  const inv={}; for(const [name,m] of Object.entries(thresholds)) (inv[m]??=[]).push(name);
  if(inv[0]) for(const name of inv[0]) out.at[name]={m:0,g:0n,mu:abs(D0)};
  for(let k=1;k<=maxm;k++){
    let S=0n;
    const amin=Math.max(0,k-1-J), amax=Math.min(k-1,n-K);
    for(let a=amin;a<=amax;a++){
      const b=k-1-a;
      S+=chK[a]*L[K+a]*chJ[b]*gMinus[J-b];
    }
    const num=BigInt(K)*S;
    if(num%BigInt(k)!==0n) throw new Error(`minus division n=${n} k=${k}`);
    const D=num/BigInt(k);
    g=gcd(g,D);
    if(inv[k]) for(const name of inv[k]) out.at[name]={m:k,g,mu:centered(D0,g)};
  }
  return out;
}
function qPlusArray(n,L,maxq){
  const q=Array(maxq+1).fill(0n);
  for(let k=0;k<=n;k++){
    let c=1n, lim=Math.min(k,maxq);
    for(let m=0;m<=lim;m++){
      q[m]+=L[k]*c;
      if(m<lim) c=c*BigInt(k-m)/BigInt(m+1);
    }
  }
  return q;
}
function momentsPlus(n,L,J,K,thresholds){
  const maxm=Math.max(...Object.values(thresholds));
  const maxq=Math.min(n,K+maxm-1), q=qPlusArray(n,L,maxq);
  const chJ=chooseRow(J), chK=chooseKArray(K,maxm);
  let D0=0n; for(let u=0;u<=J;u++) D0+=q[u]*gPlus[u];
  let g=0n;
  const out={D0,at:{}};
  const inv={}; for(const [name,m] of Object.entries(thresholds)) (inv[m]??=[]).push(name);
  if(inv[0]) for(const name of inv[0]) out.at[name]={m:0,g:0n,mu:abs(D0)};
  for(let k=1;k<=maxm;k++){
    let S=0n;
    const amin=Math.max(0,k-1-J), amax=Math.min(k-1,n-K);
    for(let a=amin;a<=amax;a++){
      const b=k-1-a;
      const term=chK[a]*q[K+a]*chJ[b]*gPlus[J-b];
      S+=(b&1)?-term:term;
    }
    const num=BigInt(K)*S;
    if(num%BigInt(k)!==0n) throw new Error(`plus division n=${n} k=${k}`);
    const D=num/BigInt(k);
    g=gcd(g,D);
    if(inv[k]) for(const name of inv[k]) out.at[name]={m:k,g,mu:centered(D0,g)};
  }
  return out;
}

function factorString(x){
  x=abs(x); if(x===1n) return '1';
  const out=[];
  for(const p of primes){
    const P=BigInt(p); if(P*P>x) break;
    let e=0; while(x%P===0n){x/=P;e++;}
    if(e) out.push(e===1?`${p}`:`${p}^${e}`);
  }
  if(x>1n) out.push(x.toString());
  return out.join('*');
}
function topRad(x,n){
  x=abs(x); let R=1n;
  for(const p of primes) if(2*p>n&&p<=n&&x%BigInt(p)===0n) R*=BigInt(p);
  return R;
}
function describe(H,n){ return {value:H.toString(),factor:factorString(H),rate:fmt(logBig(H)/n)}; }

for(const n of TARGETS){
  const J=Math.floor((n-1)/3), K=J+1, L=Lrow(n), data=candidateData(n);
  const thresholds={
    direct:safeM(data.pDirect,n),
    reflected:safeM(data.pReflected,n),
    directStruct:safeM(data.pDirectStruct,n),
    reflectedStruct:safeM(data.pReflectedStruct,n)
  };
  const mn=momentsMinus(n,L,J,K,thresholds), pl=momentsPlus(n,L,J,K,thresholds);
  const Bm=binom(n,K), Bp=binom(n+K,K);
  const keyD='directStruct', keyR='reflectedStruct';
  const Hdm=gcd(Bm,mn.at[keyD].mu), Hdp=gcd(Bm,pl.at[keyD].mu);
  const Hrm=gcd(Bp,mn.at[keyR].mu), Hrp=gcd(Bp,pl.at[keyR].mu);
  const combos=[
    {sD:'-',sR:'-',value:lcm(Hdm,Hrm)},
    {sD:'-',sR:'+',value:lcm(Hdm,Hrp)},
    {sD:'+',sR:'-',value:lcm(Hdp,Hrm)},
    {sD:'+',sR:'+',value:lcm(Hdp,Hrp)}
  ].sort((a,b)=>a.value<b.value?-1:a.value>b.value?1:0);
  const common=[{sign:'-',value:lcm(Hdm,Hrm)},{sign:'+',value:lcm(Hdp,Hrp)}]
    .sort((a,b)=>a.value<b.value?-1:a.value>b.value?1:0);
  const badRows=data.rows.filter(x=>x.bad);
  const badRad=badRows.reduce((z,x)=>z*BigInt(x.p),1n);
  for(const H of [Hdm,Hdp,Hrm,Hrp]){
    if(topRad(H,n)!==badRad) throw new Error(`top support mismatch n=${n} H=${H}`);
  }
  console.log(`N=${n} J=${J} K=${K}`);
  console.log('cutoffs',JSON.stringify({
    direct:thresholds.direct,reflected:thresholds.reflected,
    directStruct:thresholds.directStruct,reflectedStruct:thresholds.reflectedStruct,
    leastDirect:data.pDirect,leastReflected:data.pReflected,
    leastDirectStruct:data.pDirectStruct,leastReflectedStruct:data.pReflectedStruct
  }));
  console.log('bad_top',badRows.map(x=>({p:x.p,j:x.j,direct:x.direct,reflected:x.reflected})));
  console.log('H_direct_minus',JSON.stringify(describe(Hdm,n)));
  console.log('H_direct_plus ',JSON.stringify(describe(Hdp,n)));
  console.log('H_reflect_minus',JSON.stringify(describe(Hrm,n)));
  console.log('H_reflect_plus ',JSON.stringify(describe(Hrp,n)));
  console.log('best_common_sign',JSON.stringify({sign:common[0].sign,...describe(common[0].value,n)}));
  console.log('best_independent_signs',JSON.stringify({sD:combos[0].sD,sR:combos[0].sR,...describe(combos[0].value,n)}));
  console.log('all_sign_combos',JSON.stringify(combos.map(x=>({sD:x.sD,sR:x.sR,...describe(x.value,n)}))));
  console.log('moment_rates',JSON.stringify({
    minusDirectMu:fmt(logBig(mn.at[keyD].mu)/n),plusDirectMu:fmt(logBig(pl.at[keyD].mu)/n),
    minusRefMu:fmt(logBig(mn.at[keyR].mu)/n),plusRefMu:fmt(logBig(pl.at[keyR].mu)/n),
    minusDirectG:fmt(logBig(mn.at[keyD].g)/n),plusDirectG:fmt(logBig(pl.at[keyD].g)/n),
    minusRefG:fmt(logBig(mn.at[keyR].g)/n),plusRefG:fmt(logBig(pl.at[keyR].g)/n)
  }));
  console.log('---');
}
