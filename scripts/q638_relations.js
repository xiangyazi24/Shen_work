#!/usr/bin/env node
'use strict';
const NMAX=Number(process.env.RELMAX||2500);
function abs(a){return a<0n?-a:a;} function gcd(a,b){a=abs(a);b=abs(b);while(b){let r=a%b;a=b;b=r;}return a;}
function Lrow(n){const a=Array(n+1).fill(0n);a[0]=1n;for(let k=0;k<n;k++)a[k+1]=a[k]*BigInt(n-k)*BigInt(n+k+1)/(BigInt(k+1)**2n);return a;}
function chooseRow(n){const a=Array(n+1).fill(0n);a[0]=1n;for(let k=0;k<n;k++)a[k+1]=a[k]*BigInt(n-k)/BigInt(k+1);return a;}
const JMAX=Math.floor((NMAX-1)/3)+2,F=Array(JMAX+1).fill(0n);F[0]=1n;F[1]=2n;
for(let m=1;m<JMAX;m++){let M=BigInt(m);F[m+1]=((7n*M*M+7n*M+2n)*F[m]+8n*M*M*F[m-1])/(BigInt(m+1)**2n);}
const A=Array(NMAX+1).fill(0n);A[0]=1n;A[1]=5n;for(let n=1;n<NMAX;n++){let N=BigInt(n);A[n+1]=((34n*N**3n+51n*N**2n+27n*N+5n)*A[n]-N**3n*A[n-1])/(BigInt(n+1)**3n);}
let failA=null,failL=null,failBoth=null,maxA=0,maxL=0,maxBoth=0,nontrivialK=[];
for(let n=3;n<=NMAX;n++){
 const J=Math.floor((n-1)/3),K=J+1,L=Lrow(n),chJ=chooseRow(J); let C0=0n;for(let i=0;i<=J;i++)C0+=L[i]*F[i];
 const g=Array(J+1);for(let b=0;b<=J;b++)g[b]=((b&1)?-1n:1n)*chJ[b]*F[J-b];
 const q=Array(n-K+1);let ch=1n;for(let a=0;a<=n-K;a++){if(a)ch=ch*BigInt(K+a)/BigInt(a);q[a]=L[K+a]*ch;}
 let G=abs(C0),da=0,dl=0,db=0;const carrier=L[K];
 for(let d=1;d<=n;d++){
   let s=0n,amin=Math.max(0,d-1-J),amax=Math.min(n-K,d-1);for(let a=amin;a<=amax;a++)s+=q[a]*g[d-1-a];
   let cd=BigInt(K)*s/BigInt(d);G=gcd(G,cd);
   if(!da&&A[n]%G===0n)da=d;if(!dl&&carrier%G===0n)dl=d;if(!db&&A[n]%G===0n&&carrier%G===0n)db=d;
   if(da&&dl)break;
 }
 maxA=Math.max(maxA,da||n);maxL=Math.max(maxL,dl||n);maxBoth=Math.max(maxBoth,db||n);
 if(!da&&!failA)failA=[n,G.toString()];if(!dl&&!failL)failL=[n,G.toString(),gcd(G,carrier).toString()];if(!db&&!failBoth)failBoth=[n,G.toString()];
 if(gcd(G,BigInt(K))>1n)nontrivialK.push([n,K,gcd(G,BigInt(K)).toString(),da,dl]);
 if(n%250===0)console.error('rel',n,maxA,maxL);
}
console.log(JSON.stringify({NMAX,failA,failL,failBoth,maxA,maxL,maxBoth,nontrivialK:nontrivialK.slice(0,100),nontrivialKCount:nontrivialK.length}));
