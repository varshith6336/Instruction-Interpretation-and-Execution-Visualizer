// ---------- Instruction set: 8-bit word = [4-bit opcode | 4-bit operand] ----------
const OPS = [
 {c:0,m:'HLT',op:false,name:'Halt the processor',rtl:['HALT ← 1']},
 {c:1,m:'LDA',op:true,name:'Load accumulator from memory',rtl:['MAR ← IR[3:0]','MDR ← M[MAR]','AC ← MDR']},
 {c:2,m:'STA',op:true,name:'Store accumulator to memory',rtl:['MAR ← IR[3:0]','MDR ← AC','M[MAR] ← MDR']},
 {c:3,m:'ADD',op:true,name:'Add memory word to accumulator',rtl:['MAR ← IR[3:0]','MDR ← M[MAR]','AC ← AC + MDR']},
 {c:4,m:'SUB',op:true,name:'Subtract memory word from accumulator',rtl:['MAR ← IR[3:0]','MDR ← M[MAR]','AC ← AC − MDR']},
 {c:5,m:'AND',op:true,name:'Bitwise AND memory word with accumulator',rtl:['MAR ← IR[3:0]','MDR ← M[MAR]','AC ← AC ∧ MDR']},
 {c:6,m:'OR', op:true,name:'Bitwise OR memory word with accumulator',rtl:['MAR ← IR[3:0]','MDR ← M[MAR]','AC ← AC ∨ MDR']},
 {c:7,m:'JMP',op:true,name:'Unconditional jump',rtl:['PC ← IR[3:0]']},
 {c:8,m:'LDI',op:true,name:'Load immediate value into accumulator',rtl:['AC ← IR[3:0]']},
 {c:9,m:'JZ', op:true,name:'Jump if zero flag is set',rtl:['if (Z = 1) then PC ← IR[3:0]']}
];
const BY_M = Object.fromEntries(OPS.map(o=>[o.m,o]));
const SAMPLE = `LDI 9      ; AC <- 9
ADD 14     ; AC <- AC + M[14]
STA 15     ; M[15] <- AC
LDA 15     ; AC <- M[15]
SUB 13     ; AC <- AC - M[13]  (result 0, Z = 1)
JZ 7       ; Z = 1, so jump to address 7
LDI 1      ; skipped by the jump
OR 14      ; AC <- AC OR M[14]
HLT
DATA 14 3
DATA 13 12`;

const $ = id => document.getElementById(id);
const bin = (v,n) => (v>>>0).toString(2).padStart(n,'0');
const disasm = byte => { const o = OPS[byte>>4]; if(!o) return '(illegal opcode)'; return o.op ? `${o.m} ${byte&15}` : o.m; };

// ---------- CPU state ----------
let mem=new Array(16).fill(0), dataCells=new Set(), initMem=mem.slice(), initData=new Set();
let PC=0,MAR=0,MDR=0,IR=0,AC=0,Z=0,halted=false,queue=[],phase='',signals=[],hotRegs=[],memHot=false,flash=-1;
let instCount=0, stepCount=0, timer=null, started=false;

// ---------- Assembler ----------
function assemble(text){
  const out=new Array(16).fill(0), data=new Set(); let addr=0;
  const lines=text.split('\n');
  for(let i=0;i<lines.length;i++){
    const raw=lines[i].split(';')[0].trim(); if(!raw) continue;
    const p=raw.toUpperCase().split(/[\s,]+/), m=p[0];
    if(m==='DATA'){
      const a=Number(p[1]), v=Number(p[2]);
      if(!Number.isInteger(a)||a<0||a>15) throw `Line ${i+1}: DATA address must be 0–15`;
      if(!Number.isInteger(v)||v<0||v>255) throw `Line ${i+1}: DATA value must be 0–255`;
      out[a]=v; data.add(a); continue;
    }
    const o=BY_M[m]; if(!o) throw `Line ${i+1}: unknown mnemonic "${p[0]}"`;
    let x=0;
    if(o.op){ x=Number(p[1]); if(p[1]===undefined||!Number.isInteger(x)||x<0||x>15) throw `Line ${i+1}: ${m} needs an operand 0–15`; }
    if(addr>15) throw `Line ${i+1}: program does not fit in 16 memory words`;
    out[addr++]=(o.c<<4)|x;
  }
  for(const a of data) if(a<addr) throw `DATA address ${a} overlaps the program (program uses 0–${addr-1})`;
  return {out,data};
}

// ---------- Micro-operation generator ----------
function fetchSteps(){
  const T=(regs,sig,run,txt,mem)=>({ph:'Fetch',regs,sig,run,txt,mem});
  return [
    T(['PC','MAR'],['PC out','MAR in'],()=>{MAR=PC},()=>`T0: MAR ← PC          (MAR = ${bin(MAR,4)})`),
    T(['MAR','MDR'],['MEM read','MDR in'],()=>{MDR=mem[MAR]},()=>`T1: MDR ← M[MAR]      (MDR = ${bin(MDR,8)})`,true),
    T(['PC'],['PC increment'],()=>{PC=(PC+1)&15},()=>`T2: PC ← PC + 1       (PC = ${bin(PC,4)})`),
    T(['MDR','IR'],['MDR out','IR in'],()=>{IR=MDR},()=>`T3: IR ← MDR          (IR = ${bin(IR,8)})`),
    {ph:'Decode',regs:['IR'],sig:['Opcode decoder'],run:()=>{queue.push(...execSteps(IR>>4,IR&15))},
     txt:()=>{const o=OPS[IR>>4]; return o?`T4: Decode IR → opcode ${bin(IR>>4,4)} (${o.m}), operand ${bin(IR&15,4)}`:`T4: Decode IR → opcode ${bin(IR>>4,4)} is ILLEGAL`}}
  ];
}
function execSteps(op,x){
  const S=[]; let n=5;
  const T=(regs,sig,run,txt,mem)=>S.push({ph:'Execute',regs,sig,run,txt:()=>`T${n++}: `+txt(),mem});
  const rd=()=>{
    T(['IR','MAR'],['IR addr out','MAR in'],()=>{MAR=x},()=>`MAR ← IR[3:0]     (MAR = ${bin(MAR,4)})`);
    T(['MAR','MDR'],['MEM read','MDR in'],()=>{MDR=mem[MAR]},()=>`MDR ← M[MAR]      (MDR = ${bin(MDR,8)} = ${MDR})`,true);
  };
  const setAC=v=>{AC=v&255;Z=AC===0?1:0};
  const alu=(sym,f)=>{rd();T(['AC','MDR','Z'],['ALU '+sym,'AC in','Z update'],()=>setAC(f(AC,MDR)),()=>`AC ← AC ${sym} MDR   (AC = ${bin(AC,8)} = ${AC}, Z = ${Z})`)};
  switch(op){
    case 0: T(['IR'],['HALT'],()=>{halted=true},()=>'HALT ← 1          (processor stopped)'); break;
    case 1: rd(); T(['MDR','AC','Z'],['MDR out','AC in'],()=>setAC(MDR),()=>`AC ← MDR          (AC = ${bin(AC,8)} = ${AC})`); break;
    case 2:
      T(['IR','MAR'],['IR addr out','MAR in'],()=>{MAR=x},()=>`MAR ← IR[3:0]     (MAR = ${bin(MAR,4)})`);
      T(['AC','MDR'],['AC out','MDR in'],()=>{MDR=AC},()=>`MDR ← AC          (MDR = ${bin(MDR,8)})`);
      T(['MDR','MAR'],['MDR out','MEM write'],()=>{mem[MAR]=MDR;flash=MAR},()=>`M[MAR] ← MDR      (M[${MAR}] = ${MDR})`,true); break;
    case 3: alu('+',(a,b)=>a+b); break;
    case 4: alu('−',(a,b)=>a-b); break;
    case 5: alu('∧',(a,b)=>a&b); break;
    case 6: alu('∨',(a,b)=>a|b); break;
    case 7: T(['IR','PC'],['IR addr out','PC load'],()=>{PC=x},()=>`PC ← IR[3:0]      (PC = ${bin(PC,4)})`); break;
    case 8: T(['IR','AC','Z'],['IR addr out','AC in'],()=>setAC(x),()=>`AC ← IR[3:0]      (AC = ${bin(AC,8)} = ${AC})`); break;
    case 9: T(['IR','PC'],['Z test'],()=>{if(Z)PC=x},()=>Z?`Z = 1, so PC ← IR[3:0] (PC = ${bin(PC,4)})`:`Z = 0, so no jump (PC unchanged)`); break;
    default: T(['IR'],['ILLEGAL'],()=>{halted=true},()=>'Illegal opcode – processor halted');
  }
  return S;
}

// ---------- Stepping ----------
function doStep(){
  if(halted) return false;
  if(!queue.length){ queue=fetchSteps(); instCount++; }
  const s=queue.shift(); flash=-1;
  s.run(); stepCount++; started=true;
  phase=s.ph; signals=s.sig; hotRegs=s.regs; memHot=!!s.mem;
  const cls=s.ph==='Fetch'?'f':s.ph==='Decode'?'d':'e';
  const d=document.createElement('div'); d.className=cls;
  d.textContent=`[${s.ph.toUpperCase()}] `+s.txt(); $('log').appendChild(d);
  if(halted){const h=document.createElement('div');h.className='h';h.textContent='— Execution finished —';$('log').appendChild(h);}
  $('log').scrollTop=1e9; render(); return !halted;
}
function runInstruction(){ do{ if(!doStep()) break; }while(queue.length); }
function runAll(){
  if(timer){clearInterval(timer);timer=null;$('all').textContent='Run All';return;}
  $('all').textContent='Pause';
  timer=setInterval(()=>{ if(!doStep()||stepCount>600){clearInterval(timer);timer=null;$('all').textContent='Run All';} },320);
}

// ---------- Rendering ----------
function decodeHTML(byte){
  const o=OPS[byte>>4], b=bin(byte,8);
  const bits=[...b].map((c,i)=>`<div class="bit ${i<4?'o':'a'}">${c}</div>`).join('');
  let h=`<div class="bits">${bits}</div>
  <div class="kv"><span>Opcode (bits 7–4)</span><span class="mono">${b.slice(0,4)} = ${byte>>4}</span>
  <span>Operand (bits 3–0)</span><span class="mono">${b.slice(4)} = ${byte&15}</span>
  <span>Mnemonic</span><span class="mono"><b>${o?(o.op?o.m+' '+(byte&15):o.m):'—'}</b></span>
  <span>Meaning</span><span>${o?o.name:'Illegal opcode – no instruction defined'}</span></div>`;
  if(o) h+=`<ol class="rtl">${o.rtl.map(r=>`<li>${r}</li>`).join('')}</ol>`;
  return h;
}
function render(){
  const set=(id,v,n,extra)=>{const e=$('r-'+id);e.querySelector('.bin').textContent=bin(v,n);e.querySelector('.dec').textContent=extra||('= '+v);e.classList.toggle('hot',hotRegs.includes(id));};
  set('PC',PC,4);set('MAR',MAR,4);set('MDR',MDR,8);
  set('IR',IR,8,started?disasm(IR):'—');set('AC',AC,8);set('Z',Z,1,Z?'zero':'non-zero');
  for(const p of ['Fetch','Decode','Execute']) $('p-'+p).classList.toggle('on',phase===p);
  $('sigs').innerHTML=signals.map(s=>`<span class="sig">${s}</span>`).join('');
  $('stats').textContent=`Instructions started: ${instCount}   |   Micro-operations executed: ${stepCount}   |   Status: ${halted?'HALTED':'READY'}`;
  $('step').disabled=$('inst').disabled=halted; if(halted&&!timer)$('all').disabled=true; else $('all').disabled=false;
  $('decOut').innerHTML=started?decodeHTML(IR):'<p class="hint">Run the program to see each instruction decoded here.</p>';
  $('mem').innerHTML=mem.map((v,a)=>{
    let c=''; if(a===PC&&!halted) c+='pc '; if(started&&a===MAR&&hotRegs.includes('MAR')) c+='mar '; if(memHot&&a===MAR) c+='memhot '; if(a===flash) c+='flash ';
    const tags=(a===PC&&!halted?'<span class="tag p">PC</span>':'')+(started&&a===MAR&&hotRegs.includes('MAR')?'<span class="tag m">MAR</span>':'');
    return `<tr class="${c}"><td class="mono">${bin(a,4)} (${a})${tags}</td><td class="mono">${bin(v,8)}</td><td class="mono">${v}</td><td class="mono">${dataCells.has(a)?'<span class="tag d">data</span>':disasm(v)}</td></tr>`;
  }).join('');
}

// ---------- Load / reset ----------
function loadProgram(){
  try{
    const {out,data}=assemble($('src').value);
    initMem=out.slice(); initData=data; $('asmMsg').className='msg okc';
    $('asmMsg').textContent='Assembled successfully – program loaded into memory.';
    resetCPU();
  }catch(e){ $('asmMsg').className='msg err'; $('asmMsg').textContent=String(e); }
}
function resetCPU(){
  if(timer){clearInterval(timer);timer=null;$('all').textContent='Run All';}
  mem=initMem.slice(); dataCells=new Set(initData);
  PC=MAR=MDR=IR=AC=Z=0; halted=false; queue=[]; phase=''; signals=[]; hotRegs=[]; memHot=false; flash=-1;
  instCount=stepCount=0; started=false; $('log').innerHTML=''; render();
}
function interpretOne(){
  const t=$('one').value.trim().toUpperCase(), msg=$('oneMsg'); msg.className='msg err'; $('oneOut').innerHTML='';
  let byte;
  if(/^[01]{8}$/.test(t.replace(/\s/g,''))) byte=parseInt(t.replace(/\s/g,''),2);
  else{
    const p=t.split(/[\s,]+/), o=BY_M[p[0]];
    if(!o){msg.textContent='Enter a mnemonic (e.g. ADD 14) or an 8-bit binary word.';return;}
    let x=0; if(o.op){x=Number(p[1]); if(p[1]===undefined||!Number.isInteger(x)||x<0||x>15){msg.textContent=`${o.m} needs an operand between 0 and 15.`;return;}}
    byte=(o.c<<4)|x;
  }
  msg.className='msg okc'; msg.textContent=`Machine word: ${bin(byte,8)}  (decimal ${byte}, hex ${byte.toString(16).toUpperCase().padStart(2,'0')})`;
  $('oneOut').innerHTML=decodeHTML(byte);
}

$('asm').onclick=loadProgram;
$('sample').onclick=()=>{$('src').value=SAMPLE;loadProgram();};
$('step').onclick=doStep; $('inst').onclick=runInstruction; $('all').onclick=runAll; $('reset').onclick=resetCPU;
$('interp').onclick=interpretOne; $('one').addEventListener('keydown',e=>{if(e.key==='Enter')interpretOne();});
$('src').value=SAMPLE; loadProgram(); interpretOne();
