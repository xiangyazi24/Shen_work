#!/usr/bin/env node
'use strict';

const TARGETS=[400,600,800], NMAX=800, PMAX=1800;
function abs(a){return a<0n?-a:a;} function gcd(a,b){a=abs(a);b=abs(b);while(b){let r=a%b;a=b;b=r;}return a;}
function modPos(a,m){let r=a%m;return r<0n?r+m:r;} function minBig(a,b){return a<b?a:b;}
function centered(D,g){g=abs(g);if(g===0n)return abs(D);let r=modPos(D,g);if(r===0n)return g;return minBig(r,g-r);}
function logBig(a){a=abs(a);if(a===0n)return-Infinity;let s=a.toString(),t=Math.min(16,s.length);return(s.length-t)*Math.LN10+Math.log(Number(s.slice(0,t)));}
function fmt(x){return Number.isFinite(x)?x.toFixed(12):String(x);}
function sieve(n){let a=Array(n+1).fill(true);a[0]=a[1]=false;for(let p=2;p*p<=n;p++)if(a[p])for(let k=p*p;k<=n;k+=p)a[k]=false;return Array.from({length:n+1},(_,i)=>i).filter(i=>a[i]);}
const primes=sieve(PMAX);
function binom(n,k){if(k<0||k>n)return 0n;k=Math.min(k,n-k);let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-k+i)/BigInt(i);return x;}
function factor(x){x=abs(x);if(x===1n)return'1';let z=[];for(const p of primes){let P=BigInt(p);if(P*P>x)break;let e=0;while(x%P===0n){x/=P;e++;}if(e)z.push(e===1?`${p}`:`${p}^${e}`);}if(x>1n)z.push(x.toString());return z.join('*');}

const JMAX=Math.floor((NMAX-1)/3)+2,F=Array(JMAX+1).fill(0n),gp=Array(JMAX+1).fill(0n),gm=Array(JMAX+1).fill(0n);
let row=[1n];
for(let m=0;m<=JMAX;m++){
  F[m]=row.reduce((s,c)=>s+c*c*c,0n);let p=0n,q=0n;
  for(let i=0;i<=m;i++){q+=row[i]*F[i];p+=((m-i)&1?-1n:1n)*row[i]*F[i];}
  gp[m]=p;gm[m]=q;let nr=Array(m+2).fill(0n);for(let i=0;i<=m;i++){nr[i]+=row[i];nr[i+1]+=row[i];}row=nr;
}
function Lrow(n){let L=Array(n+1).fill(0n);L[0]=1n;for(let k=0;k<n;k++){let num=L[k]*BigInt(n-k)*BigInt(n+k+1),den=BigInt(k+1)**2n;if(num%den)throw Error('L');L[k+1]=num/den;}return L;}
function chooseRow(n){let a=Array(n+1).fill(0n);a[0]=1n;for(let k=0;k<n;k++)a[k+1]=a[k]*BigInt(n-k)/BigInt(k+1);return a;}
function chooseK(K,m){let a=Array(m+1).fill(0n);a[0]=1n;for(let x=0;x<m;x++)a[x+1]=a[x]*BigInt(K+x+1)/BigInt(x+1);return a;}
function qPlus(n,L,mx){let q=Array(mx+1).fill(0n);for(let k=0;k<=n;k++){let c=1n,lim=Math.min(k,mx);for(let u=0;u<=lim;u++){q[u]+=L[k]*c;if(u<lim)c=c*BigInt(k-u)/BigInt(u+1);}}return q;}

function moments(n,L,J,K,m,eps){
  let cJ=chooseRow(J),cK=chooseK(K,m),D0=0n,g=0n;
  if(eps==='-'){
    for(let u=0;u<=J;u++)D0+=(((n+u)&1)?-1n:1n)*L[u]*gm[u];
    for(let k=1;k<=m;k++){
      let S=0n,amin=Math.max(0,k-1-J),amax=Math.min(k-1,n-K);
      for(let a=amin;a<=amax;a++){let b=k-1-a;S+=cK[a]*L[K+a]*cJ[b]*gm[J-b];}
      let num=BigInt(K)*S;if(num%BigInt(k))throw Error('minus');let D=num/BigInt(k);g=gcd(g,D);
    }
  }else{
    let q=qPlus(n,L,Math.min(n,K+m-1));for(let u=0;u<=J;u++)D0+=q[u]*gp[u];
    for(let k=1;k<=m;k++){
      let S=0n,amin=Math.max(0,k-1-J),amax=Math.min(k-1,n-K);
      for(let a=amin;a<=amax;a++){let b=k-1-a,t=cK[a]*q[K+a]*cJ[b]*gp[J-b];S+=(b&1)?-t:t;}
      let num=BigInt(K)*S;if(num%BigInt(k))throw Error('plus');let D=num/BigInt(k);g=gcd(g,D);
    }
  }
  let mu=centered(D0,g);return{D0,g,mu};
}
function branchCutoffs(n,K){
  let d=[],r=[];for(const p of primes)if(2*p>n&&p<=n){let a=n-p,b=p-1-a,j=Math.min(a,b);if(a<=b&&j>=2)d.push(p);if(b<=a&&j>=2)r.push(p);}
  return{d:(d.length?Math.min(...d)-1:n),r:(r.length?Math.min(...r)-1:n)};
}
function desc(x,n){return{x:x.toString(),factor:factor(x),rate:fmt(logBig(x)/n)};}
for(const n of TARGETS){
  let J=Math.floor((n-1)/3),K=J+1,L=Lrow(n),m=branchCutoffs(n,K),Bm=binom(n,K),Bp=binom(n+K,K);
  console.log(`N=${n} mD=${m.d} mR=${m.r}`);
  for(const [branch,B,cut] of [['D',Bm,m.d],['R',Bp,m.r]])for(const eps of ['-','+']){
    let M=moments(n,L,J,K,cut,eps),H=gcd(B,M.mu),core=gcd(B,gcd(M.D0,M.g));
    if(H%core!==0n)throw Error('core does not divide centered');
    console.log(`${branch}${eps}`,JSON.stringify({H:desc(H,n),core:desc(core,n),overshoot:desc(H/core,n),gcdBD0:desc(gcd(B,M.D0),n),gcdBg:desc(gcd(B,M.g),n)}));
  }
  console.log('---');
}
