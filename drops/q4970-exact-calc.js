function abs(x){return x<0n?-x:x}
function gcd(a,b){a=abs(a);b=abs(b);while(b){let t=a%b;a=b;b=t}return a}
function pw(a,e){a=BigInt(a);e=BigInt(e);let r=1n;while(e){if(e&1n)r*=a;a*=a;e>>=1n}return r}
class R{
  constructor(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('den0');if(d<0n){n=-n;d=-d}if(!n){this.n=0n;this.d=1n;return}let g=gcd(n,d);this.n=n/g;this.d=d/g}
  static f(x){return x instanceof R?x:new R(x)}
  add(x){x=R.f(x);return new R(this.n*x.d+x.n*this.d,this.d*x.d)}
  sub(x){x=R.f(x);return new R(this.n*x.d-x.n*this.d,this.d*x.d)}
  mul(x){x=R.f(x);return new R(this.n*x.n,this.d*x.d)}
  div(x){x=R.f(x);return new R(this.n*x.d,this.d*x.n)}
  neg(){return new R(-this.n,this.d)} zero(){return this.n===0n}
  eq(x){x=R.f(x);return this.n===x.n&&this.d===x.d}
  ab(){return new R(abs(this.n),this.d)} one(){return this.n===this.d}
  s(){return this.d===1n?`${this.n}`:`${this.n}/${this.d}`}
  tex(){return this.d===1n?`${this.n}`:`\\frac{${this.n}}{${this.d}}`}
  ap(){return Number(this.n)/Number(this.d)}
}
const z=()=>new R(0n),o=()=>new R(1n);
function mom(s,k){return new R(1n,pw(BigInt(k+1),BigInt(s)))}
function solve(A,b){let n=A.length,M=A.map((r,i)=>r.slice().concat([b[i]]));for(let c=0;c<n;c++){let p=c;while(p<n&&M[p][c].zero())p++;if(p===n)throw Error('singular '+c);[M[c],M[p]]=[M[p],M[c]];let v=M[c][c];for(let j=c;j<=n;j++)M[c][j]=M[c][j].div(v);for(let i=0;i<n;i++)if(i!==c&&!M[i][c].zero()){let f=M[i][c];for(let j=c;j<=n;j++)M[i][j]=M[i][j].sub(f.mul(M[c][j]))}}return M.map(r=>r[n])}
function qp(n){if(!n)return[o()];let a=Math.ceil(n/2),b=Math.floor(n/2),A=[],v=[];for(let k=0;k<a;k++){A.push(Array.from({length:n},(_,i)=>mom(2,i+k)));v.push(mom(2,n+k).neg())}for(let k=0;k<b;k++){A.push(Array.from({length:n},(_,i)=>mom(3,i+k)));v.push(mom(3,n+k).neg())}return solve(A,v).concat([o()])}
function cf(p,i){return i>=0&&i<p.length?p[i]:z()}
function sub(a,b){let n=Math.max(a.length,b.length);return Array.from({length:n},(_,i)=>cf(a,i).sub(cf(b,i)))}
function sc(a,c){return a.map(x=>x.mul(c))}
function xt(a){return[z()].concat(a)}
function at1(a){return a.reduce((s,x)=>s.add(x),z())}
function harm(i,s){let r=z();for(let j=1;j<=i;j++)r=r.add(new R(1n,pw(BigInt(j),BigInt(s))));return r}
function pk(a,s){let r=z();for(let i=1;i<a.length;i++)r=r.add(a[i].mul(harm(i,s)));return r}
function ptex(p){let q=[];for(let k=p.length-1;k>=0;k--){let c=p[k];if(c.zero())continue;let neg=c.n<0n,a=c.ab(),cs=a.tex(),t;if(k===0)t=cs;else{if(a.one())cs='';t=cs+(k===1?'t':`t^{${k}}`)}q.push((q.length?(neg?' - ':' + '):(neg?'-':''))+t)}return q.join('')}
const N=12,Q=[];for(let n=0;n<=N;n++){let p=qp(n);Q.push(p);let a=Math.ceil(n/2),b=Math.floor(n/2);for(let k=0;k<a;k++){let s=z();for(let i=0;i<=n;i++)s=s.add(p[i].mul(mom(2,i+k)));if(!s.zero())throw Error('mu2')}for(let k=0;k<b;k++){let s=z();for(let i=0;i<=n;i++)s=s.add(p[i].mul(mom(3,i+k)));if(!s.zero())throw Error('mu3')}}
const rec=[];for(let n=0;n<N;n++){let r=sub(xt(Q[n]),Q[n+1]),be=cf(r,n);r=sub(r,sc(Q[n],be));let ga=n?cf(r,n-1):z();if(n)r=sub(r,sc(Q[n-1],ga));let de=n>=2?cf(r,n-2):z();if(n>=2)r=sub(r,sc(Q[n-2],de));if(r.some(x=>!x.zero()))throw Error('not 4term n='+n);rec.push({be,ga,de,a:o().sub(be),b:ga.neg(),c:de.neg()})}
function pev(cs,x){let r=0n;for(let c of cs)r=r*x+BigInt(c);return r}
function A(n){let x=BigInt(n);return 1024n*pw(2n*x+5n,4n)*pw(2n*x+7n,3n)*pw(2n*x+9n,3n)*pev([946,6407,10860],x)}
function B(n){let x=BigInt(n);return 128n*pw(2n*x+7n,3n)*pw(2n*x+9n,3n)*pev([104060,1745370,12145238,44886481,92943995,102256019,46709052],x)}
function C(n){let x=BigInt(n);return 16n*pw(x+3n,4n)*pw(2n*x+9n,3n)*pev([3784,57792,351019,1059230,1587211,944620],x)}
function D(n){let x=BigInt(n);return pw(x+3n,4n)*pw(x+4n,6n)*pev([946,4515,5399],x)}
const ta=n=>new R(B(n),A(n)),tb=n=>new R(-C(n-1),A(n-1)),tc=n=>new R(D(n-2),A(n-2));
let TP=[new R(-612218384750n),new R(-9525021973931919n,18100n),new R(-29561828382772029n,65380n)],TQ=[new R(-215040420000n),new R(-167282265043404n,905n),new R(-964185327658080n,6071n)];for(let n=2;n<7;n++){TP[n+1]=ta(n).mul(TP[n]).add(tb(n).mul(TP[n-1])).add(tc(n).mul(TP[n-2]));TQ[n+1]=ta(n).mul(TQ[n]).add(tb(n).mul(TQ[n-1])).add(tc(n).mul(TQ[n-2]))}
function gtest(s){let h=n=>ta(n).div(rec[n+s].a),rb=[],rc=[];for(let n=3;n<=6;n++)rb.push(tb(n).sub(h(n).mul(h(n-1)).mul(rec[n+s].b)));for(let n=4;n<=6;n++)rc.push(tc(n).sub(h(n).mul(h(n-1)).mul(h(n-2)).mul(rec[n+s].c)));return{b:rb.every(x=>x.zero()),c:rc.every(x=>x.zero()),rb:rb[0],rc:rc[0]}}
console.log('ANSWER-CALC Q4970\n');
console.log('## Polynomials');for(let n=0;n<=8;n++)console.log(`- $Q_{${n}}(t)=${ptex(Q[n])}$.`);
console.log('\n## Recurrence\n|n|beta|gamma|delta|\n|---:|---:|---:|---:|');for(let n=0;n<=6;n++)console.log(`|${n}|$${rec[n].be.tex()}$|$${rec[n].ga.tex()}$|$${rec[n].de.tex()}$|`);
console.log('\n## Approximants\n|n|Q(1)|P2(1)|P3(1)|ratio|decimal|\n|---:|---:|---:|---:|---:|---:|');let MR=[];for(let n=0;n<=8;n++){let y=at1(Q[n]),p2=pk(Q[n],2),p3=pk(Q[n],3),r=p2.add(p3).div(y);MR.push(r);console.log(`|${n}|$${y.tex()}$|$${p2.tex()}$|$${p3.tex()}$|$${r.tex()}$|${r.ap().toPrecision(16)}|`)}
console.log('\n## Target ratios\n|n|ratio|decimal|\n|---:|---:|---:|');for(let n=0;n<TP.length;n++){let r=TP[n].div(TQ[n]);console.log(`|${n}|$${r.tex()}$|${r.ap().toPrecision(16)}|`)}
let ep=[];for(let n=0;n<3;n++)for(let k=0;k<=8;k++)if(TP[n].div(TQ[n]).eq(MR[k]))ep.push([n,k]);console.log('\nExact target/MOP ratio matches for target n=0..2 and MOP k=0..8: '+(ep.length?JSON.stringify(ep):'none')+'.');
console.log('\n## Gauge tests\n|shift s|B identities n=3..6|C identities n=4..6|first B residual|first C residual|\n|---:|:---:|:---:|---:|---:|');for(let s=0;s<=3;s++){let x=gtest(s);console.log(`|${s}|${x.b}|${x.c}|$${x.rb.tex()}$|$${x.rc.tex()}$|`)}
