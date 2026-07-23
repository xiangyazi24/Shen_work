#!/usr/bin/env node
'use strict';

// Q605 exact BigInt computation. No floating arithmetic enters the integer scan.
// We use the identity
//   T_n'(c) = K q_K^{(c)} g_{K-1}^{(c)},  K=floor((n-1)/3)+1,
// to generate Taylor moments without first constructing every coefficient C_d.

const NMAX = Number(process.env.NMAX || 800);
const SAMPLE = new Set([30,40,50,60,75,80,100,120,150,180,200,240,250,300,321,350,400,450,500,600,700,800].filter(n=>n<=NMAX));

function abs(a){ return a < 0n ? -a : a; }
function gcd(a,b){ a=abs(a); b=abs(b); while(b){ const r=a%b; a=b; b=r; } return a; }
function lcm(a,b){ if(a===0n||b===0n) return 0n; return abs((a/gcd(a,b))*b); }
function modPos(a,m){ let r=a%m; if(r<0n) r+=m; return r; }
function minBig(a,b){ return a<b?a:b; }
function logBig(a){
  a=abs(a); if(a===0n) return -Infinity;
  const s=a.toString();
  const take=Math.min(16,s.length);
  const lead=Number(s.slice(0,take));
  return (s.length-take)*Math.LN10 + Math.log(lead);
}
function fmt(x,d=9){ return Number.isFinite(x)?x.toFixed(d):String(x); }

function sieve(n){
  const is=Array(n+1).fill(true); is[0]=is[1]=false;
  for(let p=2;p*p<=n;p++) if(is[p]) for(let k=p*p;k<=n;k+=p) is[k]=false;
  return {is, primes:Array.from({length:n+1},(_,i)=>i).filter(i=>is[i])};
}
const {primes} = sieve(NMAX+10);

function binom(n,k){
  if(k<0||k>n) return 0n;
  k=Math.min(k,n-k);
  let x=1n;
  for(let i=1;i<=k;i++) x = x*BigInt(n-k+i)/BigInt(i);
  return x;
}

// Pascal rows, Franel numbers, and the two binomial transforms needed at c=+/-1.
const JMAX=Math.floor((NMAX-1)/3)+2;
const F=Array(JMAX+1).fill(0n);
const gPlus=Array(JMAX+1).fill(0n);   // g_m^(+1)=sum (-1)^(m-i) C(m,i) F_i
const gMinus=Array(JMAX+1).fill(0n);  // g_m^(-1)=sum C(m,i) F_i
let row=[1n];
for(let m=0;m<=JMAX;m++){
  let fm=0n;
  for(const c of row) fm += c*c*c;
  F[m]=fm;
  let gp=0n, gm=0n;
  for(let i=0;i<=m;i++){
    gm += row[i]*F[i];
    gp += ((m-i)&1 ? -1n:1n)*row[i]*F[i];
  }
  gPlus[m]=gp; gMinus[m]=gm;
  const next=Array(m+2).fill(0n);
  for(let i=0;i<=m;i++){ next[i]+=row[i]; next[i+1]+=row[i]; }
  row=next;
}

// Exact Apéry numbers for verification of bad support.
const Apery=Array(NMAX+1).fill(0n); Apery[0]=1n; if(NMAX>=1) Apery[1]=5n;
for(let n=1;n<NMAX;n++){
  const N=BigInt(n);
  const poly=34n*N*N*N + 51n*N*N + 27n*N + 5n;
  const num=poly*Apery[n] - N*N*N*Apery[n-1];
  const den=BigInt(n+1)**3n;
  if(num%den!==0n) throw new Error('Apery recurrence nonintegral at '+n);
  Apery[n+1]=num/den;
}

function Lrow(n){
  const L=Array(n+1).fill(0n); L[0]=1n;
  for(let k=0;k<n;k++){
    const num=L[k]*BigInt(n-k)*BigInt(n+k+1);
    const den=BigInt(k+1)*BigInt(k+1);
    if(num%den!==0n) throw new Error(`L recurrence nonintegral n=${n} k=${k}`);
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
  if(r===0n) return g;
  return minBig(r,g-r);
}

function candidateData(n){
  const cand=primes.filter(p=>2*p>n && p<=n);
  if(!cand.length) throw new Error('No top-half prime at n='+n);
  let Pi=1n,R=1n,Pdir=1n,Pref=1n,Rdir=1n,Rref=1n;
  let pmin=Infinity,pdir=Infinity,pref=Infinity,pbadfloor=Infinity,pdirBadFloor=Infinity,prefBadFloor=Infinity;
  const rows=[];
  for(const p of cand){
    const r=n-p;
    const s=p-1-r;
    const j=Math.min(r,s);
    const direct=r<=s;
    const reflected=s<=r;
    const bad=Apery[j]%BigInt(p)===0n;
    Pi*=BigInt(p); pmin=Math.min(pmin,p);
    if(direct){Pdir*=BigInt(p);pdir=Math.min(pdir,p);if(bad)Rdir*=BigInt(p);}
    if(reflected){Pref*=BigInt(p);pref=Math.min(pref,p);if(bad)Rref*=BigInt(p);}
    if(bad) R*=BigInt(p);
    // j=0 and j=1 are structurally harmless for p>5.
    if(j>=2){pbadfloor=Math.min(pbadfloor,p); if(direct)pdirBadFloor=Math.min(pdirBadFloor,p); if(reflected)prefBadFloor=Math.min(prefBadFloor,p);}
    rows.push({p,r,s,j,direct,reflected,bad});
  }
  return {cand,rows,Pi,R,Pdir,Pref,Rdir,Rref,pmin,pdir,pref,pbadfloor,pdirBadFloor,prefBadFloor};
}

function thresholdMap(data,n){
  const map={
    all:data.pmin-1,
    direct:Number.isFinite(data.pdir)?data.pdir-1:0,
    reflected:Number.isFinite(data.pref)?data.pref-1:0
  };
  if(Number.isFinite(data.pbadfloor)) map.struct=data.pbadfloor-1;
  if(Number.isFinite(data.pdirBadFloor)) map.directStruct=data.pdirBadFloor-1;
  if(Number.isFinite(data.prefBadFloor)) map.reflectedStruct=data.prefBadFloor-1;
  for(const k of Object.keys(map)) map[k]=Math.max(0,Math.min(n,map[k]));
  return map;
}

function momentsMinus(n,L,J,K,thresholds){
  const maxm=Math.max(...Object.values(thresholds));
  const chJ=chooseRow(J), chK=chooseKArray(K,maxm);
  let D0=0n;
  for(let u=0;u<=J;u++) D0 += (((n+u)&1)?-1n:1n)*L[u]*gMinus[u];
  let g=0n;
  const out={D0,at:{}};
  const inv={}; for(const [name,m] of Object.entries(thresholds)) (inv[m]??=[]).push(name);
  if(inv[0]) for(const name of inv[0]) out.at[name]={m:0,g:0n,mu:abs(D0)};
  for(let k=1;k<=maxm;k++){
    let S=0n;
    const amin=Math.max(0,k-1-J);
    const amax=Math.min(k-1,n-K);
    for(let a=amin;a<=amax;a++){
      const b=k-1-a;
      S += chK[a]*L[K+a]*chJ[b]*gMinus[J-b];
    }
    const num=BigInt(K)*S;
    if(num%BigInt(k)!==0n) throw new Error(`minus moment division n=${n} k=${k}`);
    const D= num/BigInt(k); // common sign omitted; gcd and centered lattice are unchanged by sign of all D_k.
    g=gcd(g,D);
    if(inv[k]) for(const name of inv[k]) out.at[name]={m:k,g,mu:centered(D0,g)};
  }
  return out;
}

function qPlusArray(n,L,maxq){
  const q=Array(maxq+1).fill(0n);
  for(let k=0;k<=n;k++){
    let c=1n;
    const lim=Math.min(k,maxq);
    for(let m=0;m<=lim;m++){
      q[m]+=L[k]*c;
      if(m<lim) c=c*BigInt(k-m)/BigInt(m+1);
    }
  }
  return q;
}
function momentsPlus(n,L,J,K,thresholds){
  const maxm=Math.max(...Object.values(thresholds));
  const maxq=Math.min(n,K+maxm-1);
  const q=qPlusArray(n,L,maxq);
  const chJ=chooseRow(J), chK=chooseKArray(K,maxm);
  let D0=0n; for(let u=0;u<=J;u++) D0+=q[u]*gPlus[u];
  let g=0n;
  const out={D0,at:{}};
  const inv={}; for(const [name,m] of Object.entries(thresholds)) (inv[m]??=[]).push(name);
  if(inv[0]) for(const name of inv[0]) out.at[name]={m:0,g:0n,mu:abs(D0)};
  for(let k=1;k<=maxm;k++){
    let S=0n;
    const amin=Math.max(0,k-1-J);
    const amax=Math.min(k-1,n-K);
    for(let a=amin;a<=amax;a++){
      const b=k-1-a;
      const term=chK[a]*q[K+a]*chJ[b]*gPlus[J-b];
      S += (b&1)?-term:term;
    }
    const num=BigInt(K)*S;
    if(num%BigInt(k)!==0n) throw new Error(`plus moment division n=${n} k=${k}`);
    const D=num/BigInt(k);
    g=gcd(g,D);
    if(inv[k]) for(const name of inv[k]) out.at[name]={m:k,g,mu:centered(D0,g)};
  }
  return out;
}

function topRadOf(x,n){
  x=abs(x); let r=1n;
  for(const p of primes) if(2*p>n && p<=n && x%BigInt(p)===0n) r*=BigInt(p);
  return r;
}
function reportOne(n,doPlus=false){
  const J=Math.floor((n-1)/3),K=J+1;
  const data=candidateData(n), th=thresholdMap(data,n), L=Lrow(n);
  const minus=momentsMinus(n,L,J,K,th);
  const all=minus.at.all;
  if(gcd(all.g,data.Pi)!==data.Pi) throw new Error('Pi not in minus g n='+n);
  if(gcd(all.mu,data.Pi)!==data.R) throw new Error('minus exact support failure n='+n);
  const Bminus=binom(n,K), Bplus=binom(n+K,K);
  const md=minus.at.direct, mr=minus.at.reflected;
  const Gd=gcd(Bminus,md.mu), Gr=gcd(Bplus,mr.mu), Gbranch=lcm(Gd,Gr);
  if(topRadOf(Gbranch,n)!==data.R) throw new Error('branch support failure n='+n);
  const rec={n,J,K,pmin:data.pmin,m:all.m,badCount:data.rows.filter(x=>x.bad).length,
    logR:logBig(data.R)/n, logMuM:logBig(all.mu)/n, logGM:logBig(all.g)/n,
    nuisanceM:logBig(all.mu/data.R)/n,
    branchM:logBig(Gbranch)/n,
    mD:md.m,mR:mr.m,
    structM:minus.at.struct?logBig(minus.at.struct.mu)/n:null,
    plus:null};
  if(doPlus){
    const plus=momentsPlus(n,L,J,K,th), pa=plus.at.all;
    if(gcd(pa.g,data.Pi)!==data.Pi) throw new Error('Pi not in plus g n='+n);
    if(gcd(pa.mu,data.Pi)!==data.R) throw new Error('plus exact support failure n='+n);
    const pd=plus.at.direct, pr=plus.at.reflected;
    const PG=lcm(gcd(Bminus,pd.mu),gcd(Bplus,pr.mu));
    rec.plus={logMu:logBig(pa.mu)/n,logG:logBig(pa.g)/n,nuisance:logBig(pa.mu/data.R)/n,branch:logBig(PG)/n};
  }
  return rec;
}

const records=[];
let extrema={minMu:[Infinity,null],maxMu:[-Infinity,null],minBranch:[Infinity,null],maxBranch:[-Infinity,null],minNuis:[Infinity,null],maxNuis:[-Infinity,null]};
for(let n=20;n<=NMAX;n++){
  const rec=reportOne(n,SAMPLE.has(n));
  records.push(rec);
  if(n>=100){
    for(const [key,field] of [['minMu','logMuM'],['maxMu','logMuM'],['minBranch','branchM'],['maxBranch','branchM'],['minNuis','nuisanceM'],['maxNuis','nuisanceM']]){
      const wantMin=key.startsWith('min'),v=rec[field];
      if((wantMin&&v<extrema[key][0])||(!wantMin&&v>extrema[key][0])) extrema[key]=[v,n];
    }
  }
  if(n%50===0) console.error('completed',n);
}

console.log('Q605 EXACT BIGINT SCAN');
console.log('NMAX='+NMAX);
console.log('columns: n J K pmin m bad logR/n log(mu_minus)/n log(g_minus)/n log(mu/R)/n branch_lcm/n mD mR [plus rates]');
for(const r of records.filter(x=>SAMPLE.has(x.n))){
  let line=[r.n,r.J,r.K,r.pmin,r.m,r.badCount,fmt(r.logR),fmt(r.logMuM),fmt(r.logGM),fmt(r.nuisanceM),fmt(r.branchM),r.mD,r.mR].join(' ');
  if(r.plus) line+=' PLUS '+[fmt(r.plus.logMu),fmt(r.plus.logG),fmt(r.plus.nuisance),fmt(r.plus.branch)].join(' ');
  console.log(line);
}
console.log('EXTREMA n>=100');
for(const [k,v] of Object.entries(extrema)) console.log(k,fmt(v[0]),'at',v[1]);
for(const n of [200,400,600,800].filter(n=>n<=NMAX)){
  const r=records[n-20];
  console.log('CHECKPOINT',n,JSON.stringify({pmin:r.pmin,m:r.m,bad:r.badCount,logR:fmt(r.logR,12),logMuMinus:fmt(r.logMuM,12),nuisanceMinus:fmt(r.nuisanceM,12),branchMinus:fmt(r.branchM,12),plus:r.plus&&Object.fromEntries(Object.entries(r.plus).map(([k,v])=>[k,fmt(v,12)]))}));
}
