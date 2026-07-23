"use strict";
const fs = require("fs");
const input = process.argv[2];
const output = process.argv[3];
if (!input || !output) throw new Error("usage: node q4970_text_to_pdf.js INPUT OUTPUT");
const raw = fs.readFileSync(input, "utf8").replace(/\r/g, "");
const logical = raw.split("\n");
const lines = [];
const width = 128;
for (const line of logical) {
  if (line.length === 0) { lines.push(""); continue; }
  let s = line;
  while (s.length > width) { lines.push(s.slice(0,width)); s=s.slice(width); }
  lines.push(s);
}
const perPage = 70;
const pages=[];
for(let i=0;i<lines.length;i+=perPage) pages.push(lines.slice(i,i+perPage));
function esc(s){ return s.replace(/\\/g,"\\\\").replace(/\(/g,"\\(").replace(/\)/g,"\\)").replace(/[^\x20-\x7E]/g,"?"); }
const objs=[];
function add(s){ objs.push(s); return objs.length; }
const catalog=add("");
const pagesObj=add("");
const font=add("<< /Type /Font /Subtype /Type1 /BaseFont /Courier >>");
const pageIds=[];
for (const pg of pages) {
  const content = ["BT","/F1 6.5 Tf","24 770 Td","8.5 TL",...pg.map((ln,i)=>`${i===0?"":"T* "}(${esc(ln)}) Tj`),"ET"].join("\n");
  const stream=add(`<< /Length ${Buffer.byteLength(content,"ascii")} >>\nstream\n${content}\nendstream`);
  const page=add("");
  pageIds.push({page,stream});
}
objs[catalog-1]=`<< /Type /Catalog /Pages ${pagesObj} 0 R >>`;
objs[pagesObj-1]=`<< /Type /Pages /Kids [${pageIds.map(x=>`${x.page} 0 R`).join(" ")}] /Count ${pageIds.length} >>`;
for(const x of pageIds) objs[x.page-1]=`<< /Type /Page /Parent ${pagesObj} 0 R /MediaBox [0 0 612 792] /Resources << /Font << /F1 ${font} 0 R >> >> /Contents ${x.stream} 0 R >>`;
let pdf="%PDF-1.4\n%\xE2\xE3\xCF\xD3\n";
const offsets=[0];
for(let i=0;i<objs.length;i++){
  offsets.push(Buffer.byteLength(pdf,"binary"));
  pdf += `${i+1} 0 obj\n${objs[i]}\nendobj\n`;
}
const xref=Buffer.byteLength(pdf,"binary");
pdf += `xref\n0 ${objs.length+1}\n0000000000 65535 f \n`;
for(let i=1;i<offsets.length;i++) pdf += `${String(offsets[i]).padStart(10,"0")} 00000 n \n`;
pdf += `trailer\n<< /Size ${objs.length+1} /Root ${catalog} 0 R >>\nstartxref\n${xref}\n%%EOF\n`;
fs.writeFileSync(output, Buffer.from(pdf,"binary"));
console.log(`wrote ${output}: ${pages.length} pages, ${lines.length} lines`);
