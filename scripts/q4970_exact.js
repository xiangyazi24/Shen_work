"use strict";

function absBI(x) { return x < 0n ? -x : x; }
function gcdBI(a,b) { a=absBI(a); b=absBI(b); while (b!==0n) { const t=a%b; a=b; b=t; } return a; }
function powBI(a,e) { a=BigInt(a); e=BigInt(e); let r=1n; while(e>0n){ if(e&1n) r*=a; a*=a; e>>=1n; } return r; }

class Rat {
  constructor(n,d=1n) {
    n=BigInt(n); d=BigInt(d);
    if (d===0n) throw new Error("zero denominator");
    if (d<0n) { n=-n; d=-d; }
    if (n===0n) { this.n=0n; this.d=1n; return; }
    const g=gcdBI(n,d); this.n=n/g; this.d=d/g;
  }
  static of(x){ return x instanceof Rat ? x : new Rat(x); }
  add(x){ x=Rat.of(x); return new Rat(this.n*x.d+x.n*this.d,this.d*x.d); }
  sub(x){ x=Rat.of(x); return new Rat(this.n*x.d-x.n*this.d,this.d*x.d); }
  mul(x){ x=Rat.of(x); return new Rat(this.n*x.n,this.d*x.d); }
  div(x){ x=Rat.of(x); return new Rat(this.n*x.d,this.d*x.n); }
  neg(){ return new Rat(-this.n,this.d); }
  abs(){ return new Rat(absBI(this.n),this.d); }
  zero(){ return this.n===0n; }
  one(){ return this.n===this.d; }
  eq(x){ x=Rat.of(x); return this.n===x.n && this.d===x.d; }
  str(){ return this.d===1n ? `${this.n}` : `${this.n}/${this.d}`; }
  tex(){ return this.d===1n ? `${this.n}` : `\\frac{${this.n}}{${this.d}}`; }
}
const Z=()=>new Rat(0n), O=()=>new Rat(1n);
function moment(s,k){ return new Rat(1n,powBI(BigInt(k+1),BigInt(s))); }

function solveLinear(A,b){
  const n=A.length;
  const M=A.map((r,i)=>r.slice().concat([b[i]]));
  for(let c=0;c<n;c++){
    let p=c; while(p<n && M[p][c].zero()) p++;
    if(p===n) throw new Error(`singular column ${c}`);
    if(p!==c){ const t=M[p]; M[p]=M[c]; M[c]=t; }
    const piv=M[c][c];
    for(let j=c;j<=n;j++) M[c][j]=M[c][j].div(piv);
    for(let r=0;r<n;r++) if(r!==c && !M[r][c].zero()){
      const f=M[r][c];
      for(let j=c;j<=n;j++) M[r][j]=M[r][j].sub(f.mul(M[c][j]));
    }
  }
  return M.map(r=>r[n]);
}

function qPolynomial(n){
  if(n===0) return [O()];
  const n2=Math.ceil(n/2), n3=Math.floor(n/2), A=[], b=[];
  for(let k=0;k<n2;k++){
    A.push(Array.from({length:n},(_,i)=>moment(2,i+k)));
    b.push(moment(2,n+k).neg());
  }
  for(let k=0;k<n3;k++){
    A.push(Array.from({length:n},(_,i)=>moment(3,i+k)));
    b.push(moment(3,n+k).neg());
  }
  return solveLinear(A,b).concat([O()]);
}
function coeff(p,i){ return i>=0 && i<p.length ? p[i] : Z(); }
function polySub(a,b){ const n=Math.max(a.length,b.length),r=[]; for(let i=0;i<n;i++) r.push(coeff(a,i).sub(coeff(b,i))); return r; }
function polyScale(a,c){ return a.map(x=>x.mul(c)); }
function polyX(a){ return [Z()].concat(a); }
function polyAtOne(a){ return a.reduce((s,x)=>s.add(x),Z()); }
function assertZeroPoly(p,label){ for(let i=0;i<p.length;i++) if(!p[i].zero()) throw new Error(`${label}: coefficient ${i}=${p[i].str()}`); }
function harmonic(i,s){ let r=Z(); for(let j=1;j<=i;j++) r=r.add(new Rat(1n,powBI(BigInt(j),BigInt(s)))); return r; }
function secondKindAtOne(p,s){ let r=Z(); for(let i=1;i<p.length;i++) r=r.add(p[i].mul(harmonic(i,s))); return r; }
function polyTex(p){
  const out=[];
  for(let k=p.length-1;k>=0;k--){
    const c=p[k]; if(c.zero()) continue;
    const neg=c.n<0n, a=c.abs(); let cs=a.tex(), term;
    if(k===0) term=cs;
    else { if(a.one()) cs=""; term=cs+(k===1?"t":`t^{${k}}`); }
    if(out.length===0) out.push((neg?"-":"")+term); else out.push((neg?" - ":" + ")+term);
  }
  return out.join("");
}

const NMAX=20;
const Q=[];
for(let n=0;n<=NMAX;n++){
  const p=qPolynomial(n); Q.push(p);
  const n2=Math.ceil(n/2),n3=Math.floor(n/2);
  for(let k=0;k<n2;k++){
    let s=Z(); for(let i=0;i<=n;i++) s=s.add(p[i].mul(moment(2,i+k)));
    if(!s.zero()) throw new Error(`mu2 orthogonality n=${n} k=${k}`);
  }
  for(let k=0;k<n3;k++){
    let s=Z(); for(let i=0;i<=n;i++) s=s.add(p[i].mul(moment(3,i+k)));
    if(!s.zero()) throw new Error(`mu3 orthogonality n=${n} k=${k}`);
  }
}

const rec=[];
for(let n=0;n<NMAX;n++){
  let r=polySub(polyX(Q[n]),Q[n+1]);
  const beta=coeff(r,n); r=polySub(r,polyScale(Q[n],beta));
  const gamma=n>=1?coeff(r,n-1):Z(); if(n>=1) r=polySub(r,polyScale(Q[n-1],gamma));
  const delta=n>=2?coeff(r,n-2):Z(); if(n>=2) r=polySub(r,polyScale(Q[n-2],delta));
  assertZeroPoly(r,`four-term n=${n}`);
  rec.push({beta,gamma,delta,a:O().sub(beta),b:gamma.neg(),c:delta.neg()});
}

function peval(cs,x){ let r=0n; for(const c of cs) r=r*x+BigInt(c); return r; }
function A27(n){ const x=BigInt(n); return 1024n*powBI(2n*x+5n,4n)*powBI(2n*x+7n,3n)*powBI(2n*x+9n,3n)*peval([946,6407,10860],x); }
function B27(n){ const x=BigInt(n); return 128n*powBI(2n*x+7n,3n)*powBI(2n*x+9n,3n)*peval([104060,1745370,12145238,44886481,92943995,102256019,46709052],x); }
function C27(n){ const x=BigInt(n); return 16n*powBI(x+3n,4n)*powBI(2n*x+9n,3n)*peval([3784,57792,351019,1059230,1587211,944620],x); }
function D27(n){ const x=BigInt(n); return powBI(x+3n,4n)*powBI(x+4n,6n)*peval([946,4515,5399],x); }
function ta(n){ return new Rat(B27(n),A27(n)); }
function tb(n){ return new Rat(-C27(n-1),A27(n-1)); }
function tc(n){ return new Rat(D27(n-2),A27(n-2)); }

const tp=[new Rat(-612218384750n),new Rat(-9525021973931919n,18100n),new Rat(-29561828382772029n,65380n)];
const tq=[new Rat(-215040420000n),new Rat(-167282265043404n,905n),new Rat(-964185327658080n,6071n)];
for(let n=2;n<8;n++){
  tp[n+1]=ta(n).mul(tp[n]).add(tb(n).mul(tp[n-1])).add(tc(n).mul(tp[n-2]));
  tq[n+1]=ta(n).mul(tq[n]).add(tb(n).mul(tq[n-1])).add(tc(n).mul(tq[n-2]));
}

function directGaugeCheck(offset){
  const detail=[];
  function h(n){ return ta(n).div(rec[n+offset].a); }
  let ok=true;
  for(let n=3;n<=6;n++){
    const db=tb(n).sub(h(n).mul(h(n-1)).mul(rec[n+offset].b));
    detail.push(`n=${n}: Bdiff=${db.str()}`); if(!db.zero()) ok=false;
    if(n>=4){ const dc=tc(n).sub(h(n).mul(h(n-1)).mul(h(n-2)).mul(rec[n+offset].c)); detail.push(`n=${n}: Cdiff=${dc.str()}`); if(!dc.zero()) ok=false; }
  }
  return {ok,detail};
}

function matMul(A,B){
  const R=Array.from({length:A.length},()=>Array.from({length:B[0].length},()=>Z()));
  for(let i=0;i<A.length;i++) for(let k=0;k<B.length;k++) for(let j=0;j<B[0].length;j++) R[i][j]=R[i][j].add(A[i][k].mul(B[k][j]));
  return R;
}
const I3=[[O(),Z(),Z()],[Z(),O(),Z()],[Z(),Z(),O()]], F={2:I3};
for(let m=2;m<NMAX;m++){
  const T=[[rec[m].a,rec[m].b,rec[m].c],[O(),Z(),Z()],[Z(),O(),Z()]];
  F[m+1]=matMul(T,F[m]);
}
function rowFor(m){ if(m===0)return[Z(),Z(),O()]; if(m===1)return[Z(),O(),Z()]; if(m===2)return[O(),Z(),Z()]; return F[m][0]; }
function contractionCoeff(n,offset){
  const rn1=rowFor(2*(n+1)+offset), r0=rowFor(2*n+offset), r1=rowFor(2*(n-1)+offset), r2=rowFor(2*(n-2)+offset);
  const M=Array.from({length:3},(_,j)=>[r0[j],r1[j],r2[j]]);
  const x=solveLinear(M,rn1); return {a:x[0],b:x[1],c:x[2]};
}
function contractionGaugeCheck(offset){
  const cr={}; for(let n=2;n<=6;n++) cr[n]=contractionCoeff(n,offset);
  function h(n){ return ta(n).div(cr[n].a); }
  let ok=true; const detail=[];
  for(let n=3;n<=6;n++){
    const db=tb(n).sub(h(n).mul(h(n-1)).mul(cr[n].b)); detail.push(`n=${n}: Bdiff=${db.str()}`); if(!db.zero())ok=false;
    if(n>=4){ const dc=tc(n).sub(h(n).mul(h(n-1)).mul(h(n-2)).mul(cr[n].c)); detail.push(`n=${n}: Cdiff=${dc.str()}`); if(!dc.zero())ok=false; }
  }
  return {ok,cr,detail};
}

console.log("ANSWER-CALC Q4970");
console.log("\n## Q_0 through Q_8");
for(let n=0;n<=8;n++) console.log(`Q_${n}(t) = ${polyTex(Q[n])}`);
console.log("\n## recurrence beta,gamma,delta n=0..6");
for(let n=0;n<=6;n++) console.log(`n=${n}: beta=${rec[n].beta.str()}, gamma=${rec[n].gamma.str()}, delta=${rec[n].delta.str()}`);
console.log("\n## values at 1 and combined second-kind numerator");
for(let n=0;n<=8;n++){
  const y=polyAtOne(Q[n]), p2=secondKindAtOne(Q[n],2), p3=secondKindAtOne(Q[n],3), r=p2.add(p3);
  console.log(`n=${n}: Q(1)=${y.str()}, P2(1)=${p2.str()}, P3(1)=${p3.str()}, R=${r.str()}`);
}
console.log("\n## target initial ratios and direct sequence comparisons");
for(let n=0;n<=5;n++) console.log(`target n=${n}: p=${tp[n].str()}, q=${tq[n].str()}, p/q=${tp[n].div(tq[n]).str()}`);
for(let off=0;off<=6;off++){
  const y=polyAtOne(Q[off]), r=secondKindAtOne(Q[off],2).add(secondKindAtOne(Q[off],3));
  console.log(`offset=${off}: initial ratio MOP=${r.div(y).str()}, target=${tp[0].div(tq[0]).str()}, difference=${r.div(y).sub(tp[0].div(tq[0])).str()}`);
}
console.log("\n## direct gauge tests");
for(let off=0;off<=6;off++){ const z=directGaugeCheck(off); console.log(`offset=${off}: ok=${z.ok}; first=${z.detail[0]}`); }
console.log("\n## two-step contraction gauge tests");
for(let off=0;off<=6;off++){
  const z=contractionGaugeCheck(off); console.log(`offset=${off}: ok=${z.ok}; first=${z.detail[0]}`);
  if(off<=2) for(let n=2;n<=4;n++) console.log(`  n=${n}: a=${z.cr[n].a.str()}, b=${z.cr[n].b.str()}, c=${z.cr[n].c.str()}`);
}
