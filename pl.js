/* Valid Moves: the languages PL and PLE (The Logic Book, ch. 7).
   Formulas use (∀x) and (∃x), predicates are capital letters followed by terms,
   constants are a–v and variables w–z (with optional subscripts), identity is a = b,
   and functors are written f(a) or h(a,b). Every binary compound needs brackets,
   except that outermost ones may be dropped.
   AST: {op:'atom',pred,args:[term]} · {op:'~',a} · {op,l,r,br} · {op:'∀'|'∃',v,a}
   term: {t:'var'|'con',n} · {t:'fn',n,args} */
(function(){
const BIN=['&','∨','⊃','≡'];
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
function fail(code,msg){const e=new Error(msg);e.code=code;return e}

function normalize(s){
  return s.replace(/<->|<=>/g,'≡').replace(/->|=>/g,'⊃')
    .replace(/[¬!−]/g,'~').replace(/[∧^·]/g,'&').replace(/\|/g,'∨')
    .replace(/(^|[\s)\]])v(?=[\s(\[~]|$)/g,'$1∨')
    .replace(/[→>]/g,'⊃').replace(/↔/g,'≡')
    .replace(/\((?:A|∀)\s*([w-z]\d*)\)/g,'(∀$1)').replace(/\((?:E|∃)\s*([w-z]\d*)\)/g,'(∃$1)')
    .replace(/(^|[^(])∀\s*([w-z]\d*)/g,'$1(∀$2)').replace(/(^|[^(])∃\s*([w-z]\d*)/g,'$1(∃$2)');
}
function tokenize(src){
  const s=normalize(src),t=[];let i=0;
  const sub=j=>{let k=j;while(k<s.length&&/[0-9]/.test(s[k]))k++;return k};
  while(i<s.length){
    const c=s[i];
    if(/\s/.test(c)){i++;continue}
    if(c==='('&&(s[i+1]==='∀'||s[i+1]==='∃')){
      const m=s.slice(i).match(/^\(([∀∃])([w-z]\d*)\)/);
      if(!m)throw fail('char','A quantifier is written (∀x) or (∃x), with a variable from w to z.');
      t.push({q:m[1],v:m[2]});i+=m[0].length;continue;
    }
    if(/[A-Z]/.test(c)){const k=sub(i+1);t.push({cap:s.slice(i,k)});i=k;continue}
    if(/[a-z]/.test(c)){const k=sub(i+1);t.push({low:s.slice(i,k)});i=k;continue}
    if('~&∨⊃≡()[]=,'.includes(c)){t.push(c);i++;continue}
    if(/[0-9]/.test(c))throw fail('char','A number can only appear as a subscript, right after a letter.');
    throw fail('char','"'+c+'" isn\'t a symbol of PL.');
  }
  if(!t.length)throw fail('empty','Type a formula.');
  return t;
}
const isVar=n=>/^[w-z]/.test(n);
function strict(t){
  let p=0;
  function term(){
    const k=t[p];
    if(!k||!k.low)throw fail('term','An individual term (a constant a–v or a variable w–z) is needed here.');
    p++;
    if(t[p]==='('&&!isVar(k.low)){
      p++;const args=[term()];
      while(t[p]===','){p++;args.push(term())}
      if(t[p]!==')')throw fail('term','A functor\'s arguments are closed with ")".');
      p++;return{t:'fn',n:k.low,args};
    }
    return{t:isVar(k.low)?'var':'con',n:k.low};
  }
  function S(){
    const k=t[p];
    if(k===undefined)throw fail('end','The expression ends where a formula is still needed.');
    if(k==='~'){p++;return{op:'~',a:S()}}
    if(k.q){p++;return{op:k.q,v:k.v,a:S()}}
    if(k.cap){p++;const args=[];while(t[p]&&t[p].low)args.push(term());return{op:'atom',pred:k.cap,args}}
    if(k.low){const l=term();if(t[p]!=='=')throw fail('term','A term on its own isn\'t a formula. Did you mean an identity like a = b, or a predicate like Fa?');p++;const r=term();return{op:'atom',pred:'=',args:[l,r]}}
    if(k==='('||k==='['){
      p++;const l=S(),op=t[p];
      if(!BIN.includes(op)){
        if(op===undefined)throw fail('end','A bracket is opened but never closed.');
        if(op===')'||op===']')throw fail('parens','Brackets go only around a compound made with a binary connective. Quantifiers are written (∀x), not with brackets around the formula.');
        throw fail('concat','Two formulas sit side by side with no connective between them.');
      }
      p++;const r=S(),c=t[p];
      if(BIN.includes(c))throw fail('multi','Each binary connective needs its own pair of brackets.');
      if(c===undefined)throw fail('end','A bracket is opened but never closed.');
      if(c!==')'&&c!==']')throw fail('concat','Two formulas sit side by side with no connective between them.');
      if((k==='('&&c!==')')||(k==='['&&c!==']'))throw fail('match','Brackets must match: ( with ) and [ with ].');
      p++;return{op,l,r,br:k};
    }
    if(BIN.includes(k))throw fail('operand','"'+k+'" needs a formula on its left and on its right.');
    if(k==='=')throw fail('operand','"=" needs a term on each side, as in a = b.');
    throw fail('stray','There\'s a closing bracket with nothing to close.');
  }
  const a=S();
  if(p<t.length){
    const k=t[p];
    if(BIN.includes(k))throw fail('outer','A compound made with "'+k+'" must be enclosed in brackets.');
    if(k===')'||k===']')throw fail('stray','There\'s a closing bracket with nothing to close.');
    throw fail('concat','Two formulas sit side by side with no connective between them.');
  }
  return a;
}
/* Clause 4: (∀x)P needs x to occur in P and P to contain no x-quantifier. */
function occursVar(n,x){if(n.op==='atom')return n.args.some(tm=>termHas(tm,x));if(n.op==='~'||n.op==='∀'||n.op==='∃')return(n.v===x&&n.op!=='~')||occursVar(n.a,x);return occursVar(n.l,x)||occursVar(n.r,x)}
function hasQ(n,x){if(n.op==='atom')return false;if(n.op==='∀'||n.op==='∃')return n.v===x||hasQ(n.a,x);if(n.op==='~')return hasQ(n.a,x);return hasQ(n.l,x)||hasQ(n.r,x)}
function termHas(tm,x){return tm.t==='fn'?tm.args.some(a=>termHas(a,x)):tm.n===x}
function validate(n){
  if(n.op==='atom')return;
  if(n.op==='~')return validate(n.a);
  if(n.op==='∀'||n.op==='∃'){
    if(!occursVar(n.a,n.v))throw fail('vacuous','('+n.op+n.v+') must be followed by a formula containing '+n.v+'. Clause 4 doesn\'t allow empty quantifiers.');
    if(hasQ(n.a,n.v))throw fail('requant','('+n.op+n.v+') is attached to a formula that already contains a '+n.v+'-quantifier, which clause 4 doesn\'t allow.');
    return validate(n.a);
  }
  validate(n.l);validate(n.r);
}
function parse(src){
  const t=tokenize(src);let ast,informal=false;
  try{ast=strict(t)}catch(e1){
    if(e1.code!=='outer')throw e1;
    try{ast=strict(['(',...t,')']);informal=true}catch(e2){throw e2.code==='multi'?fail('multi','Each binary connective needs its own pair of brackets, for example (Fa & Gb) & Hc.'):e2}
  }
  validate(ast);
  return{ast,informal};
}

/* ---------- display ---------- */
function showTerm(tm){return tm.t==='fn'?tm.n+'('+tm.args.map(showTerm).join(',')+')':tm.n}
function show(n){
  switch(n.op){
    case 'atom':return n.pred==='='?showTerm(n.args[0])+' = '+showTerm(n.args[1]):n.pred+n.args.map(showTerm).join('');
    case '~':return '~ '+show(n.a);
    case '∀':case '∃':return '('+n.op+n.v+')'+show(n.a);
    default:{const[o,c]=n.br==='['?['[',']']:['(',')'];return o+show(n.l)+' '+n.op+' '+show(n.r)+c}
  }
}
function showTop(n){const s=show(n);return BIN.includes(n.op)?s.slice(1,-1):s}
const key=n=>show(n).replace(/\[/g,'(').replace(/\]/g,')');
const eq=(a,b)=>key(a)===key(b);

/* ---------- structure ---------- */
function kind(n){return n.op==='atom'?'Atomic':(n.op==='∀'||n.op==='∃')?'Quantified':'Truth-functional'}
function immediate(n){return n.op==='atom'?[]:(n.op==='~'||n.op==='∀'||n.op==='∃')?[n.a]:[n.l,n.r]}
function subformulas(n){const out=[],seen=new Set(),q=[n];while(q.length){const x=q.shift(),k=key(x);if(!seen.has(k)){seen.add(k);out.push(x)}q.push(...immediate(x))}return out}
function freeVars(n,bound=new Set(),out=new Set()){
  if(n.op==='atom'){const walk=tm=>tm.t==='fn'?tm.args.forEach(walk):(tm.t==='var'&&!bound.has(tm.n)&&out.add(tm.n));n.args.forEach(walk);return out}
  if(n.op==='∀'||n.op==='∃'){const b=new Set(bound);b.add(n.v);return freeVars(n.a,b,out)}
  immediate(n).forEach(c=>freeVars(c,bound,out));return out;
}
const isSentence=n=>freeVars(n).size===0;
function constants(n,out=new Set()){
  const walk=tm=>tm.t==='fn'?tm.args.forEach(walk):(tm.t==='con'&&out.add(tm.n));
  if(n.op==='atom')n.args.forEach(walk);else immediate(n).forEach(c=>constants(c,out));return out;
}
function vocab(n,out={preds:{},consts:new Set(),fns:{},letters:new Set()}){
  if(n.op==='atom'){
    if(n.pred!=='='){if(n.args.length===0)out.letters.add(n.pred);else out.preds[n.pred]=n.args.length}
    const walk=tm=>{if(tm.t==='fn'){out.fns[tm.n]=tm.args.length;tm.args.forEach(walk)}else if(tm.t==='con')out.consts.add(tm.n)};
    n.args.forEach(walk);
  }else immediate(n).forEach(c=>vocab(c,out));
  return out;
}
/* P(a/x): replace free occurrences of variable x with term a. */
function substTerm(tm,x,a){return tm.t==='fn'?{t:'fn',n:tm.n,args:tm.args.map(s=>substTerm(s,x,a))}:(tm.t==='var'&&tm.n===x?a:tm)}
function subst(n,x,a){
  switch(n.op){
    case 'atom':return{op:'atom',pred:n.pred,args:n.args.map(tm=>substTerm(tm,x,a))};
    case '~':return{op:'~',a:subst(n.a,x,a)};
    case '∀':case '∃':return n.v===x?n:{op:n.op,v:n.v,a:subst(n.a,x,a)};
    default:return{op:n.op,l:subst(n.l,x,a),r:subst(n.r,x,a),br:n.br};
  }
}
/* Is `inst` a substitution instance Q(a/x) of the quantified `q`? Returns the constant or null. */
function instanceOf(q,inst){
  const cs=[...constants(inst)];
  for(const c of cs){if(eq(subst(q.a,q.v,{t:'con',n:c}),inst))return c}
  return null;
}

/* ---------- semantics on a finite interpretation ----------
   I = {ud:[0..n-1], names:[...], preds:{F:Set of 'i,j'}, letters:{A:bool}, consts:{a:i}, fns:{f:{'i,j':k}}} */
function evalTerm(tm,I,g){
  if(tm.t==='var')return g[tm.n];
  if(tm.t==='con')return I.consts[tm.n];
  const args=tm.args.map(a=>evalTerm(a,I,g));return I.fns[tm.n][args.join(',')];
}
function evaluate(n,I,g={}){
  switch(n.op){
    case 'atom':
      if(n.pred==='=')return evalTerm(n.args[0],I,g)===evalTerm(n.args[1],I,g);
      if(!n.args.length)return !!I.letters[n.pred];
      return I.preds[n.pred].has(n.args.map(a=>evalTerm(a,I,g)).join(','));
    case '~':return !evaluate(n.a,I,g);
    case '&':return evaluate(n.l,I,g)&&evaluate(n.r,I,g);
    case '∨':return evaluate(n.l,I,g)||evaluate(n.r,I,g);
    case '⊃':return !evaluate(n.l,I,g)||evaluate(n.r,I,g);
    case '≡':return evaluate(n.l,I,g)===evaluate(n.r,I,g);
    case '∀':return I.ud.every(d=>evaluate(n.a,I,{...g,[n.v]:d}));
    case '∃':return I.ud.some(d=>evaluate(n.a,I,{...g,[n.v]:d}));
  }
}
function tuples(n,k){if(k===0)return[[]];const out=[];tuples(n,k-1).forEach(t=>{for(let i=0;i<n;i++)out.push([...t,i])});return out}
/* Search interpretations with UD size 1..maxN for one where test(I) holds. */
function findModel(asts,test,maxN=3,limit=400000){
  const V={preds:{},consts:new Set(),fns:{},letters:new Set()};asts.forEach(a=>vocab(a,V));
  const preds=Object.entries(V.preds),consts=[...V.consts],fns=Object.entries(V.fns),letters=[...V.letters];
  for(let n=1;n<=maxN;n++){
    const predSlots=preds.map(([p,k])=>[p,tuples(n,k).map(t=>t.join(','))]);
    const bits=predSlots.reduce((s,[,ts])=>s+ts.length,0)+letters.length;
    const fnSlots=fns.map(([f,k])=>[f,tuples(n,k).map(t=>t.join(','))]);
    const fnCount=fnSlots.reduce((s,[,ts])=>s+ts.length,0);
    const total=Math.pow(2,bits)*Math.pow(n,consts.length+fnCount);
    if(total>limit)return{tooBig:true,n};
    for(let code=0;code<total;code++){
      let c=code;const I={ud:[...Array(n).keys()],preds:{},letters:{},consts:{},fns:{}};
      predSlots.forEach(([p,ts])=>{const S=new Set();ts.forEach(t=>{if(c%2)S.add(t);c=Math.floor(c/2)});I.preds[p]=S});
      letters.forEach(l=>{I.letters[l]=!!(c%2);c=Math.floor(c/2)});
      consts.forEach(k=>{I.consts[k]=c%n;c=Math.floor(c/n)});
      fnSlots.forEach(([f,ts])=>{const m={};ts.forEach(t=>{m[t]=c%n;c=Math.floor(c/n)});I.fns[f]=m});
      if(test(I))return{I,n,V};
    }
  }
  return null;
}
const NAMES=['1','2','3','4','5','6'];
function describe(I,V){
  const out=['UD: {'+I.ud.map(d=>NAMES[d]).join(', ')+'}'];
  [...V.consts].sort().forEach(c=>out.push(c+': '+NAMES[I.consts[c]]));
  [...V.letters].sort().forEach(l=>out.push(l+': '+(I.letters[l]?'T':'F')));
  Object.keys(V.preds).sort().forEach(p=>out.push(p+': {'+[...I.preds[p]].map(t=>t.split(',').map(i=>NAMES[i]).join(',')).map(x=>V.preds[p]>1?'<'+x+'>':x).join(', ')+'}'));
  Object.keys(V.fns).sort().forEach(f=>out.push(f+': '+Object.entries(I.fns[f]).map(([k,v])=>f+'('+k.split(',').map(i=>NAMES[i]).join(',')+') = '+NAMES[v]).join(', ')));
  return out;
}
const KEYS_HTML='<div class="keys" aria-label="Insert a symbol">'+
  [['(∀x)','Universal quantifier (type (Ax))','∀'],['(∃x)','Existential quantifier (type (Ex))','∃'],['~ ','Tilde','~'],[' & ','Ampersand','&'],[' ∨ ','Wedge (type " v ")','∨'],[' ⊃ ','Horseshoe (type >)','⊃'],[' ≡ ','Triple bar (type <->)','≡'],[' = ','Identity','='],['(','Open parenthesis','('],[')','Close parenthesis',')'],['[','Open bracket','['],[']','Close bracket',']']]
  .map(k=>'<button type="button" class="key" data-ins="'+esc(k[0])+'" title="'+esc(k[1])+'">'+k[2]+'</button>').join('')+'</div>';
function wireInput(inp,keys,onChange){
  inp.addEventListener('input',()=>{
    const pos=inp.selectionStart,before=inp.value,after=normalize(before);
    if(after!==before){const at=normalize(before.slice(0,pos)).length;inp.value=after;try{inp.setSelectionRange(at,at)}catch(e){}}
    onChange();
  });
  keys&&keys.querySelectorAll('[data-ins]').forEach(b=>b.addEventListener('click',()=>{
    const s=inp.selectionStart??inp.value.length,e=inp.selectionEnd??s,ins=b.dataset.ins;
    inp.value=inp.value.slice(0,s)+ins+inp.value.slice(e);inp.focus();
    try{inp.setSelectionRange(s+ins.length,s+ins.length)}catch(err){}
    onChange();
  }));
}
window.PL={parse,show,showTop,key,eq,kind,immediate,subformulas,freeVars,isSentence,constants,vocab,subst,instanceOf,evaluate,findModel,describe,normalize,KEYS_HTML,wireInput,NAMES,showTerm,tuples};
})();
