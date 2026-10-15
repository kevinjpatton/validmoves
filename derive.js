/* Valid Moves: derivation checker for SD and SD+ (The Logic Book, ch. 5).
   Input is plain text, one derivation line per text line:
     [line number]  | | sentence    justification
   Each "|" is one scope line. Justifications follow the book: "Assumption",
   "A / ⊃I", "1 &E", "1, 3 ⊃E", "2–4 ~I", "1, 2–4, 5–7 ∨E". An optional first line
   "Derive: P" states the goal. Requires logic.js (window.SL). */
(function(){
/* The language is SL by default; check(text, system, PL) switches to PL/PLE (ch. 10). */
let LANG=SL,parse=SL.parse,show=SL.show,normalize=SL.normalize;
const SD=['R','&I','&E','⊃I','⊃E','~I','~E','∨I','∨E','≡I','≡E'];
const INF_PLUS=['MT','HS','DS'];
const REPL=['Com','Assoc','Impl','DN','DeM','Idem','Trans','Exp','Dist','Equiv'];
const QUANT=['∀E','∀I','∃E','∃I'];
const IDENT=['=I','=E'];
const ALL=[...SD,...INF_PLUS,...REPL,...QUANT,'QN',...IDENT];
const SYSTEMS={
  'SD':SD,'SD+':[...SD,...INF_PLUS,...REPL],
  'PD':[...SD,...QUANT],'PD+':[...SD,...INF_PLUS,...REPL,...QUANT,'QN'],
  'PDE':[...SD,...QUANT,...IDENT]
};
const ALIAS={UE:'∀E',UI:'∀I',EE:'∃E',EI:'∃I',vE:'∨E',vI:'∨I'};
const key=n=>show(n).replace(/\[/g,'(').replace(/\]/g,')');
const eq=(a,b)=>key(a)===key(b);
const N=a=>({op:'~',a}),B=(op,l,r)=>({op,l,r});

/* ---------- parsing ---------- */
const RULE_RE=[...ALL,...Object.keys(ALIAS)].map(r=>r.replace(/[&~∨⊃≡]/g,m=>'\\'+m)).sort((a,b)=>b.length-a.length).join('|');
const CITE='\\d+(?:\\s*[-–—]\\s*\\d+)?';
const JUST_RE=new RegExp('^(.*?)\\s+((?:Assumption|A(?:\\s*/\\s*(?:'+RULE_RE+'))?)|(?:=I)|(?:'+CITE+'(?:\\s*,\\s*'+CITE+')*\\s*(?:'+RULE_RE+')))\\s*$');
function normRule(s){s=s.replace(/\s+/g,'');if(ALIAS[s])return ALIAS[s];return normalize(s).replace(/Equi∨/g,'Equiv').replace(/\s+/g,'')}
function parseCites(s){
  return s.split(',').map(x=>x.trim()).filter(Boolean).map(x=>{const m=x.match(/^(\d+)\s*[-–—]\s*(\d+)$/);return m?{range:true,a:+m[1],b:+m[2]}:{range:false,a:+x}});
}
function parseLine(raw){
  let s=raw.replace(/\t/g,'  ');
  const numM=s.match(/^\s*(\d+)[.)]?\s+/);let given=null;
  if(numM&&/^[\s│|]*[A-Za-z~(\[]/.test(s.slice(numM[0].length))){given=+numM[1];s=s.slice(numM[0].length)}
  let depth=0;const bar=s.match(/^[\s│|┃]*/)[0];depth=(bar.match(/[│|┃]/g)||[]).length;s=s.slice(bar.length);
  /* ASCII names for the quantifier rules: UE, UI, EE, EI */
  s=s.replace(/(\s)(UE|UI|EE|EI|vE|vI)\s*$/,(m,sp,r)=>sp+ALIAS[r]);
  s=normalize(s).replace(/Equi∨/g,'Equiv');
  /* try every justification split; keep the one whose left side is a sentence */
  const candidates=[];
  const m=s.match(JUST_RE);
  if(m)candidates.push([m[1],m[2]]);
  /* also allow the justification to be separated by 2+ spaces even if the regex above split wrongly */
  const wide=s.match(/^(.*?\S)\s{2,}(\S.*)$/);if(wide)candidates.push([wide[1],wide[2]]);
  for(const [f,j] of candidates){
    let ast;try{ast=parse(f).ast}catch(e){continue}
    const just=parseJust(j);if(just)return{given,depth,ast,just,text:f.trim(),jtext:j.trim()};
  }
  let ast=null,err=null;try{ast=parse(s).ast}catch(e){err=e.message}
  return{given,depth,ast,just:null,text:s.trim(),jtext:'',err:ast?'This line has no justification. Add one at the end, like "1 &E" or "A / ⊃I".':err};
}
function parseJust(j){
  j=j.trim();
  if(/^Assumption$/i.test(j))return{assume:true,for:null};
  if(/^=\s*I$/.test(j))return{assume:false,rule:'=I',cites:[]};
  const a=j.match(/^A(?:\s*\/\s*(.+))?$/);
  if(a){const r=a[1]?normRule(a[1]):null;if(r&&!ALL.includes(r))return null;return{assume:true,for:r}}
  const m=j.match(new RegExp('^((?:'+CITE+')(?:\\s*,\\s*'+CITE+')*)\\s*('+RULE_RE+')$'));
  if(!m)return null;
  return{assume:false,rule:normRule(m[2]),cites:parseCites(m[1])};
}

/* ---------- replacement rules: all results of rewriting one component ---------- */
function rewritesAt(x,rule){
  const out=[];
  const isN=n=>n.op==='~';
  switch(rule){
    case 'Com': if(x.op==='&'||x.op==='∨')out.push(B(x.op,x.r,x.l));break;
    case 'Assoc':
      if((x.op==='&'||x.op==='∨')&&x.r.op===x.op)out.push(B(x.op,B(x.op,x.l,x.r.l),x.r.r));
      if((x.op==='&'||x.op==='∨')&&x.l.op===x.op)out.push(B(x.op,x.l.l,B(x.op,x.l.r,x.r)));break;
    case 'Impl':
      if(x.op==='⊃')out.push(B('∨',N(x.l),x.r));
      if(x.op==='∨'&&isN(x.l))out.push(B('⊃',x.l.a,x.r));break;
    case 'DN': out.push(N(N(x)));if(isN(x)&&isN(x.a))out.push(x.a.a);break;
    case 'DeM':
      if(isN(x)&&x.a.op==='&')out.push(B('∨',N(x.a.l),N(x.a.r)));
      if(isN(x)&&x.a.op==='∨')out.push(B('&',N(x.a.l),N(x.a.r)));
      if(x.op==='∨'&&isN(x.l)&&isN(x.r))out.push(N(B('&',x.l.a,x.r.a)));
      if(x.op==='&'&&isN(x.l)&&isN(x.r))out.push(N(B('∨',x.l.a,x.r.a)));break;
    case 'Idem':
      out.push(B('&',x,x),B('∨',x,x));
      if((x.op==='&'||x.op==='∨')&&eq(x.l,x.r))out.push(x.l);break;
    case 'Trans':
      if(x.op==='⊃')out.push(B('⊃',N(x.r),N(x.l)));
      if(x.op==='⊃'&&isN(x.l)&&isN(x.r))out.push(B('⊃',x.r.a,x.l.a));break;
    case 'Exp':
      if(x.op==='⊃'&&x.r.op==='⊃')out.push(B('⊃',B('&',x.l,x.r.l),x.r.r));
      if(x.op==='⊃'&&x.l.op==='&')out.push(B('⊃',x.l.l,B('⊃',x.l.r,x.r)));break;
    case 'Dist':
      if(x.op==='&'&&x.r.op==='∨')out.push(B('∨',B('&',x.l,x.r.l),B('&',x.l,x.r.r)));
      if(x.op==='∨'&&x.r.op==='&')out.push(B('&',B('∨',x.l,x.r.l),B('∨',x.l,x.r.r)));
      if(x.op==='∨'&&x.l.op==='&'&&x.r.op==='&'&&eq(x.l.l,x.r.l))out.push(B('&',x.l.l,B('∨',x.l.r,x.r.r)));
      if(x.op==='&'&&x.l.op==='∨'&&x.r.op==='∨'&&eq(x.l.l,x.r.l))out.push(B('∨',x.l.l,B('&',x.l.r,x.r.r)));break;
    case 'Equiv':
      if(x.op==='≡')out.push(B('&',B('⊃',x.l,x.r),B('⊃',x.r,x.l)),B('∨',B('&',x.l,x.r),B('&',N(x.l),N(x.r))));
      if(x.op==='&'&&x.l.op==='⊃'&&x.r.op==='⊃'&&eq(x.l.l,x.r.r)&&eq(x.l.r,x.r.l))out.push(B('≡',x.l.l,x.l.r));
      if(x.op==='∨'&&x.l.op==='&'&&x.r.op==='&'&&isN(x.r.l)&&isN(x.r.r)&&eq(x.l.l,x.r.l.a)&&eq(x.l.r,x.r.r.a))out.push(B('≡',x.l.l,x.l.r));break;
    case 'QN':
      if(isN(x)&&(x.a.op==='∀'||x.a.op==='∃'))out.push({op:x.a.op==='∀'?'∃':'∀',v:x.a.v,a:N(x.a.a)});
      if((x.op==='∀'||x.op==='∃')&&isN(x.a))out.push(N({op:x.op==='∀'?'∃':'∀',v:x.v,a:x.a.a}));break;
  }
  return out;
}
/* Every result of rewriting exactly one subformula (rules of replacement work on subformulas). */
function oneStep(n,rule){
  const out=rewritesAt(n,rule).map(key);
  if(n.op==='atom'||n.v&&!n.op)return out;
  if(n.op==='~')oneStep(n.a,rule).forEach(k=>out.push('~ '+k));
  else if(n.op==='∀'||n.op==='∃')oneStep(n.a,rule).forEach(k=>out.push('('+n.op+n.v+')'+k));
  else if(n.op){
    const o=n.op;
    oneStep(n.l,rule).forEach(k=>out.push('('+k+' '+o+' '+key(n.r)+')'));
    oneStep(n.r,rule).forEach(k=>out.push('('+key(n.l)+' '+o+' '+k+')'));
  }
  return out;
}

/* ---------- checking ---------- */
function check(text,system,lang){
  LANG=lang||SL;parse=LANG.parse;show=LANG.show;normalize=LANG.normalize;
  const allowed=SYSTEMS[system]||SD;
  const raw=text.split('\n');
  let goal=null,goalErr=null;const lines=[];
  raw.forEach(r=>{
    if(!r.trim())return;
    const g=r.match(/^\s*Derive\s*:\s*(.+)$/i);
    if(g){try{goal=parse(g[1]).ast}catch(e){goalErr='Goal: '+e.message}return}
    lines.push(parseLine(r));
  });
  if(!lines.length)return{lines:[],goal,goalErr,summary:null};
  /* One "|" marks the main scope line. Lines typed with no bars at all also count as the main
     scope; a derivation that so far has only deeper lines (one that opens with an auxiliary
     assumption) is still measured from one bar. */
  const base=Math.min(1,...lines.map(l=>l.depth));
  lines.forEach((l,i)=>{l.n=i+1;l.d=l.depth-base;l.errs=[];if(l.err)l.errs.push(l.err);if(l.given!==null&&l.given!==l.n)l.errs.push('Numbered '+l.given+' but it is line '+l.n+'.');
    if(l.ast&&LANG.isSentence&&!LANG.isSentence(l.ast))l.errs.push('Every line of a derivation must be a sentence; this formula has a free variable.')});
  /* scope structure */
  const subs=[];let stack=[];let primaryDone=false;
  /* s.last is the 1-based number of a subderivation's last line; when line index i (0-based) closes it, that is i. */
  lines.forEach((l,i)=>{
    const isAssume=l.just&&l.just.assume;
    if(l.d===0){
      while(stack.length){const s=stack.pop();s.last=i}
      if(isAssume){if(primaryDone)l.errs.push('Primary assumptions go at the top of the derivation. An assumption made later needs its own scope line.')}
      else primaryDone=true;
    }else{
      primaryDone=true;
      while(stack.length&&stack[stack.length-1].d>l.d){const s=stack.pop();s.last=i}
      const top=stack[stack.length-1];
      if(isAssume&&top&&top.d===l.d){stack.pop();top.last=i}
      const cur=stack[stack.length-1];const curD=cur?cur.d:0;
      if(l.d>curD){
        if(!isAssume||l.d!==curD+1){l.errs.push(isAssume?'A new subderivation goes exactly one scope line further in.':'A new scope line must begin with an assumption.')}
        const s={start:i+1,d:l.d,parent:cur||null,assumeFor:l.just&&l.just.assume?l.just.for:null};
        subs.push(s);stack.push(s);
        if(isAssume&&!l.just.for)l.errs.push('Say which rule will discharge this assumption, like "A / ⊃I".');
      }
    }
    l.chain=[...stack];
  });
  while(stack.length){const s=stack.pop();s.last=lines.length}
  const isPrefix=(a,b)=>a.length<=b.length&&a.every((x,i)=>x===b[i]);
  const lineAcc=(j,i)=>j<i&&isPrefix(lines[j-1].chain,lines[i-1].chain);
  const subAcc=(s,i)=>s.last<i&&isPrefix(s.parent?chainOf(s.parent):[],lines[i-1].chain);
  function chainOf(s){const c=[];let x=s;while(x){c.unshift(x);x=x.parent}return c}
  /* checks */
  lines.forEach(l=>{
    if(!l.ast||!l.just)return;
    if(l.just.assume)return;
    const r=l.just.rule;
    if(!allowed.includes(r)){
      const home=['SD','SD+','PD','PD+','PDE'].find(s=>SYSTEMS[s].includes(r));
      l.errs.push(r+' is not a rule of '+system+(home?' (it belongs to '+home+').':'.'));return}
    const lc=[],rc=[];
    for(const c of l.just.cites){
      if(c.range){
        const s=subs.find(s=>s.start===c.a&&s.last===c.b);
        if(!s){l.errs.push(c.a+'–'+c.b+' is not a subderivation. A cited range must run from an auxiliary assumption to the last line of its subderivation.');return}
        if(!subAcc(s,l.n)){l.errs.push('Subderivation '+c.a+'–'+c.b+' is not accessible at line '+l.n+'.');return}
        rc.push(s);
      }else{
        if(c.a<1||c.a>=l.n){l.errs.push('Line '+c.a+' does not come before line '+l.n+'.');return}
        if(!lineAcc(c.a,l.n)){l.errs.push('Line '+c.a+' is not accessible at line '+l.n+': it is inside a subderivation that has ended.');return}
        if(!lines[c.a-1].ast){l.errs.push('Line '+c.a+' has no sentence to cite.');return}
        lc.push(lines[c.a-1].ast);
      }
    }
    /* assumptions open at this line: primary ones plus the assumption of every enclosing subderivation */
    const openAs=[...lines.filter(x=>x.d===0&&x.just&&x.just.assume&&x.n<l.n),...l.chain.map(s=>lines[s.start-1])].map(x=>x.ast).filter(Boolean);
    const msg=ruleCheck(r,l.ast,lc,rc,lines,openAs);
    if(msg)l.errs.push(msg);
  });
  /* assumptions annotated for a rule should be discharged by that rule */
  subs.forEach(s=>{
    const user=lines.slice(s.last).find(l=>l.just&&!l.just.assume&&l.just.cites.some(c=>c.range&&c.a===s.start&&c.b===s.last));
    if(!user){lines[s.start-1].warn='This subderivation is never cited, so its assumption is never discharged.'}
    else if(s.assumeFor&&user.just.rule!==s.assumeFor)lines[s.start-1].warn='Annotated for '+s.assumeFor+' but discharged by '+user.just.rule+' on line '+user.n+'.';
  });
  const errors=lines.filter(l=>l.errs.length).length;
  const last=lines[lines.length-1];
  const prim=lines.filter(l=>l.d===0&&l.just&&l.just.assume).map(l=>l.ast);
  let summary;
  if(errors)summary={ok:false,text:errors+' line'+(errors>1?'s need':' needs')+' fixing.'};
  else if(last.d!==0)summary={ok:false,text:'The derivation ends inside a subderivation. The last line must be back on the main scope line.'};
  else if(goal&&!eq(goal,last.ast))summary={ok:false,text:'Every line checks out, but the last line is not the goal '+LANG.showTop(goal)+'.'};
  else summary={ok:true,prim,concl:last.ast,text:''};
  return{lines,goal,goalErr,summary,subs,lang:LANG};
}
function findSubParts(s,lines){
  const first=lines[s.start-1],lastL=lines[s.last-1];
  const top=lines.slice(s.start-1,s.last).filter(l=>l.chain[l.chain.length-1]===s&&l.ast);
  return{assume:first.ast,last:lastL.ast,top:top.map(l=>l.ast),lastAtTop:lastL.chain[lastL.chain.length-1]===s};
}
function ruleCheck(r,f,L,S,lines,openAs){
  const need=(nl,ns)=>L.length!==nl||S.length!==ns?r+' cites '+(nl?nl+' line'+(nl>1?'s':''):'')+(nl&&ns?' and ':'')+(ns?ns+' subderivation'+(ns>1?'s':''):'')+'.':null;
  let e;
  switch(r){
    case 'R': if(e=need(1,0))return e;return eq(L[0],f)?null:'Reiteration repeats an accessible line exactly.';
    case '&I': if(e=need(2,0))return e;return f.op==='&'&&((eq(f.l,L[0])&&eq(f.r,L[1]))||(eq(f.l,L[1])&&eq(f.r,L[0])))?null:'&I joins the two cited sentences as P & Q.';
    case '&E': if(e=need(1,0))return e;return L[0].op==='&'&&(eq(L[0].l,f)||eq(L[0].r,f))?null:'&E takes one conjunct of a cited conjunction. Rules of inference apply to whole lines only.';
    case '∨I': if(e=need(1,0))return e;return f.op==='∨'&&(eq(f.l,L[0])||eq(f.r,L[0]))?null:'∨I adds a disjunct: from P derive P ∨ Q or Q ∨ P.';
    case '⊃E': if(e=need(2,0))return e;
      return [[0,1],[1,0]].some(([i,j])=>L[i].op==='⊃'&&eq(L[i].l,L[j])&&eq(L[i].r,f))?null:'⊃E needs P ⊃ Q and P, and gives Q.';
    case '≡E': if(e=need(2,0))return e;
      return [[0,1],[1,0]].some(([i,j])=>L[i].op==='≡'&&((eq(L[i].l,L[j])&&eq(L[i].r,f))||(eq(L[i].r,L[j])&&eq(L[i].l,f))))?null:'≡E needs P ≡ Q and one side, and gives the other side.';
    case '⊃I':{if(e=need(0,1))return e;const p=findSubParts(S[0],lines);
      if(!p.lastAtTop)return'The cited subderivation must end on its own scope line.';
      return f.op==='⊃'&&eq(f.l,p.assume)&&eq(f.r,p.last)?null:'⊃I: from a subderivation of Q from assumption P, derive P ⊃ Q.'}
    case '~I': case '~E':{if(e=need(0,1))return e;const p=findSubParts(S[0],lines);
      const has=p.top.some(q=>p.top.some(nq=>nq.op==='~'&&eq(nq.a,q)));
      if(!has)return r+' needs both a sentence Q and its negation ~ Q on the subderivation\'s own scope line.';
      if(r==='~I')return f.op==='~'&&eq(f.a,p.assume)?null:'~I: from assumption P leading to Q and ~ Q, derive ~ P.';
      return p.assume.op==='~'&&eq(p.assume.a,f)?null:'~E: from assumption ~ P leading to Q and ~ Q, derive P.'}
    case '∨E':{if(e=need(1,2))return e;if(L[0].op!=='∨')return'∨E cites a disjunction and two subderivations.';
      const a=findSubParts(S[0],lines),b=findSubParts(S[1],lines);
      if(!a.lastAtTop||!b.lastAtTop)return'Each cited subderivation must end on its own scope line.';
      const okA=(eq(a.assume,L[0].l)&&eq(b.assume,L[0].r))||(eq(a.assume,L[0].r)&&eq(b.assume,L[0].l));
      if(!okA)return'∨E: one subderivation assumes the left disjunct, the other the right disjunct.';
      return eq(a.last,f)&&eq(b.last,f)?null:'∨E: both subderivations must end with the sentence entered on this line.'}
    case '≡I':{if(e=need(0,2))return e;const a=findSubParts(S[0],lines),b=findSubParts(S[1],lines);
      if(!a.lastAtTop||!b.lastAtTop)return'Each cited subderivation must end on its own scope line.';
      if(f.op!=='≡')return'≡I derives a biconditional.';
      const ok=(eq(a.assume,f.l)&&eq(a.last,f.r)&&eq(b.assume,f.r)&&eq(b.last,f.l))||(eq(b.assume,f.l)&&eq(b.last,f.r)&&eq(a.assume,f.r)&&eq(a.last,f.l));
      return ok?null:'≡I: one subderivation goes from P to Q, the other from Q to P; then derive P ≡ Q.'}
    case 'MT': if(e=need(2,0))return e;
      return [[0,1],[1,0]].some(([i,j])=>L[i].op==='⊃'&&L[j].op==='~'&&eq(L[j].a,L[i].r)&&f.op==='~'&&eq(f.a,L[i].l))?null:'MT: from P ⊃ Q and ~ Q derive ~ P.';
    case 'HS': if(e=need(2,0))return e;
      return [[0,1],[1,0]].some(([i,j])=>L[i].op==='⊃'&&L[j].op==='⊃'&&eq(L[i].r,L[j].l)&&f.op==='⊃'&&eq(f.l,L[i].l)&&eq(f.r,L[j].r))?null:'HS: from P ⊃ Q and Q ⊃ R derive P ⊃ R.';
    case 'DS': if(e=need(2,0))return e;
      return [[0,1],[1,0]].some(([i,j])=>L[i].op==='∨'&&L[j].op==='~'&&((eq(L[j].a,L[i].l)&&eq(f,L[i].r))||(eq(L[j].a,L[i].r)&&eq(f,L[i].l))))?null:'DS: from P ∨ Q and ~ P derive Q (or from ~ Q derive P).';
    /* ---------- PD: quantifier rules ---------- */
    case '∀E':{if(e=need(1,0))return e;const q=L[0];
      if(q.op!=='∀')return'∀E cites a universally quantified sentence.';
      return closedTerms(f).some(t=>eq(PL.subst(q.a,q.v,t),f))?null:'∀E: enter a substitution instance P(a/x) of the cited sentence, replacing every '+q.v+' with the same term.'}
    case '∃I':{if(e=need(1,0))return e;
      if(f.op!=='∃')return'∃I derives an existentially quantified sentence.';
      return closedTerms(L[0]).some(t=>eq(PL.subst(f.a,f.v,t),L[0]))?null:'∃I: the cited line must be a substitution instance of the sentence entered.'}
    case '∀I':{if(e=need(1,0))return e;
      if(f.op!=='∀')return'∀I derives a universally quantified sentence.';
      const cands=[...PL.constants(L[0])].filter(a=>eq(PL.subst(f.a,f.v,{t:'con',n:a}),L[0]));
      if(!cands.length)return'∀I: the cited line must be a substitution instance P(a/x) of the sentence entered.';
      const ok=cands.find(a=>!PL.constants(f).has(a)&&!openAs.some(x=>PL.constants(x).has(a)));
      if(ok)return null;
      const a=cands[0],inOpen=openAs.some(x=>PL.constants(x).has(a));
      if(PL.constants(f).has(a))return'∀I restriction (ii): the instantiating constant '+a+' must not occur in the universal sentence derived.'+(inOpen?' It also occurs in an open assumption, breaking restriction (i).':'');
      return'∀I restriction (i): the instantiating constant '+a+' occurs in an assumption that is still open.'}
    case '∃E':{if(e=need(1,1))return e;const q=L[0];
      if(q.op!=='∃')return'∃E cites an existentially quantified sentence and a subderivation.';
      const p=findSubParts(S[0],lines);
      if(!p.lastAtTop)return'The cited subderivation must end on its own scope line.';
      if(!eq(p.last,f))return'∃E: enter the sentence the subderivation ends with.';
      const cands=[...PL.constants(p.assume)].filter(a=>eq(PL.subst(q.a,q.v,{t:'con',n:a}),p.assume));
      if(!cands.length)return'∃E: the subderivation must assume a substitution instance P(a/x) of the existential sentence.';
      const ok=cands.find(a=>!PL.constants(q).has(a)&&!PL.constants(f).has(a)&&!openAs.some(x=>PL.constants(x).has(a)));
      if(ok)return null;
      const a=cands[0];
      if(PL.constants(q).has(a))return'∃E restriction (ii): the instantiating constant '+a+' must not occur in the existential sentence.';
      if(PL.constants(f).has(a))return'∃E restriction (iii): the instantiating constant '+a+' must not occur in the sentence derived.';
      return'∃E restriction (i): the instantiating constant '+a+' occurs in an assumption that is still open.'}
    /* ---------- PDE: identity ---------- */
    case '=I': if(L.length||S.length)return'=I cites no lines.';
      return f.op==='∀'&&f.a.op==='atom'&&f.a.pred==='='&&f.a.args.every(t=>t.t==='var'&&t.n===f.v)?null:'=I enters a sentence of the form (∀x)x = x.';
    case '=E':{if(e=need(2,0))return e;
      for(const [i,j] of [[0,1],[1,0]]){const id=L[i],P=L[j];
        if(id.op!=='atom'||id.pred!=='=')continue;
        const[t1,t2]=id.args;
        if(replacedSome(P,f,t1,t2)||replacedSome(P,f,t2,t1))return null}
      return'=E: from t₁ = t₂ and a sentence P, enter P with one or more occurrences of one term replaced by the other.'}
    default:
      if(REPL.includes(r)||r==='QN'){if(e=need(1,0))return e;
        return oneStep(L[0],r).includes(key(f))?null:r+' doesn\'t turn the cited sentence into this one with a single replacement. Each replacement needs its own line, and the component must match the rule\'s form exactly.'}
      return'Unknown rule.';
  }
}
/* closed terms (no variables) occurring in a PL formula */
function closedTerms(n,out=[]){
  const st=PL.showTerm,seen=new Set(out.map(st));
  const hasVar=t=>t.t==='var'||(t.t==='fn'&&t.args.some(hasVar));
  const walk=t=>{if(!hasVar(t)&&!seen.has(st(t))){seen.add(st(t));out.push(t)}if(t.t==='fn')t.args.forEach(walk)};
  (function go(x){if(x.op==='atom')x.args.forEach(walk);else if(x.op==='~'||x.op==='∀'||x.op==='∃')go(x.a);else{go(x.l);go(x.r)}})(n);
  return out;
}
/* Is g just like p except that one or more occurrences of term s are replaced by t? */
function replacedSome(p,g,s,t){
  const st=PL.showTerm,S=st(s),T=st(t);let diffs=0;
  function term(a,b){const A=st(a),Bt=st(b);if(A===Bt)return true;if(A===S&&Bt===T){diffs++;return true}
    if(a.t==='fn'&&b.t==='fn'&&a.n===b.n&&a.args.length===b.args.length)return a.args.every((x,i)=>term(x,b.args[i]));return false}
  function f(a,b){
    if(a.op!==b.op)return false;
    if(a.op==='atom')return a.pred===b.pred&&a.args.length===b.args.length&&a.args.every((x,i)=>term(x,b.args[i]));
    if(a.op==='~')return f(a.a,b.a);
    if(a.op==='∀'||a.op==='∃')return a.v===b.v&&f(a.a,b.a);
    return f(a.l,b.l)&&f(a.r,b.r);
  }
  return f(p,g)&&diffs>0;
}
/* Fitch-style rendering: one scope line per level, a rule under each assumption block. */
function render(res){
  const esc=SL.esc,L=res.lines,TOP=(res.lang||SL).showTop;
  let h='';
  if(res.goal)h+='<div class="goalrow">Derive: <span class="f">'+esc(TOP(res.goal))+'</span></div>';
  if(res.goalErr)h+='<div class="fmsg">'+esc(res.goalErr)+'</div>';
  L.forEach((l,i)=>{
    const nx=L[i+1];
    const isA=l.just&&l.just.assume;
    const underline=isA&&(l.d>0||!(nx&&nx.d===0&&nx.just&&nx.just.assume));
    const st=l.errs.length?'<span class="fk no" title="Needs fixing">✗</span>':l.warn?'<span class="fk warn" title="Note">!</span>':'<span class="fk ok" title="Checks out">✓</span>';
    h+='<div class="frow'+(l.errs.length?' bad':'')+'"><span class="fn">'+l.n+'</span><span class="fb">'+'<span class="bar"></span>'.repeat(l.d+1)+
      '<span class="fs'+(underline?' assume':'')+'">'+(l.ast?esc(TOP(l.ast)):esc(l.text))+'</span></span><span class="fj">'+esc(l.jtext||'')+'</span>'+st+
      (l.errs.length?'<div class="fmsg">'+l.errs.map(esc).join(' ')+'</div>':l.warn?'<div class="fmsg w">'+esc(l.warn)+'</div>':'')+'</div>';
  });
  return '<div class="fitch">'+h+'</div>';
}
window.SDX={check,render,SD,INF_PLUS,REPL,ALL,parseLine};
})();
