/* Valid Moves: shared logic for every page.
   Sentences follow the syntax of SL in The Logic Book (6th ed.), section 2.1:
   capital letters with optional numeric subscripts, ~ & ∨ ⊃ ≡, and parentheses
   (or square brackets) around every binary compound. Outer parentheses may be
   dropped informally, as the book allows. */
(function(){
const BIN=['&','∨','⊃','≡'];
const KIND={'~':'Negation','&':'Conjunction','∨':'Disjunction','⊃':'Material conditional','≡':'Material biconditional'};
const CLAUSE={'~':2,'&':3,'∨':4,'⊃':5,'≡':6};
const NAME={'~':'tilde','&':'ampersand','∨':'wedge','⊃':'horseshoe','≡':'triple bar'};

const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const store={
  get(k,d){try{const v=localStorage.getItem(k);return v?JSON.parse(v):d}catch(e){return d}},
  set(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}
};

/* Turn keyboard shortcuts and other textbooks' symbols into the book's. */
function normalize(s){
  return s.replace(/<->|<=>/g,'≡').replace(/->|=>/g,'⊃')
    .replace(/[¬!−]/g,'~').replace(/[∧^·]/g,'&').replace(/[|v]/g,'∨')
    .replace(/[→>]/g,'⊃').replace(/[↔=]/g,'≡');
}
function fail(code,msg){const e=new Error(msg);e.code=code;return e}
function tokenize(src){
  const s=normalize(src),t=[];let i=0;
  while(i<s.length){
    const c=s[i];
    if(/\s/.test(c)){i++;continue}
    if(/[A-Z]/.test(c)){let j=i+1;while(j<s.length&&/[0-9]/.test(s[j]))j++;const sub=s.slice(i+1,j);
      if(sub&&/^0/.test(sub)) throw fail('char','Subscripts on sentence letters are positive integers, so "'+s.slice(i,j)+'" isn\'t a sentence letter.');
      t.push({v:s.slice(i,j)});i=j;continue}
    if('~&∨⊃≡()[]'.includes(c)){t.push(c);i++;continue}
    if(/[0-9]/.test(c)) throw fail('char','A number can only appear as a subscript right after a capital letter, as in A1.');
    if(/[a-z]/.test(c)) throw fail('char','Sentence letters of SL are capital letters A to Z (with optional subscripts, like A1). "'+c+'" is lowercase.');
    throw fail('char','"'+c+'" isn\'t a symbol of SL. SL uses sentence letters, ~ & ∨ ⊃ ≡, and brackets.');
  }
  if(!t.length) throw fail('empty','Type an expression to check.');
  return t;
}
const isAtomTok=k=>k&&typeof k==='object';
function strict(t){
  let p=0;
  function S(){
    const k=t[p];
    if(k===undefined) throw fail('end','The expression ends where a sentence is still needed.');
    if(isAtomTok(k)){p++;return{v:k.v}}
    if(k==='~'){p++;return{op:'~',a:S()}}
    if(k==='('||k==='['){
      p++;const l=S(),op=t[p];
      if(!BIN.includes(op)){
        if(op===undefined) throw fail('end','A bracket is opened but never closed.');
        if(op===')'||op===']') throw fail('parens','Brackets go only around a compound made with a binary connective. "(A)" and "(~ A)" are not sentences of SL.');
        throw fail('concat','Two sentences sit side by side with no connective between them. No clause of the definition allows that.');
      }
      p++;const r=S(),c=t[p];
      if(BIN.includes(c)) throw fail('multi','One pair of brackets can hold only one binary connective at its top level. Add brackets to show the grouping, for example ((A & B) & C).');
      if(c===undefined) throw fail('end','A bracket is opened but never closed.');
      if(c!==')'&&c!==']') throw fail('concat','Two sentences sit side by side with no connective between them. No clause of the definition allows that.');
      if((k==='('&&c!==')')||(k==='['&&c!==']')) throw fail('match','A "'+k+'" is closed with "'+c+'". Brackets must match: ( with ) and [ with ].');
      p++;return{op,l,r,br:k};
    }
    if(BIN.includes(k)) throw fail('operand','The '+NAME[k]+' "'+k+'" is binary: it needs a sentence on its left and on its right.');
    throw fail('stray','There\'s a closing bracket with nothing to close.');
  }
  const a=S();
  if(p<t.length){
    const k=t[p];
    if(BIN.includes(k)) throw fail('outer','A compound made with "'+k+'" must be enclosed in brackets.');
    if(k===')'||k===']') throw fail('stray','There\'s a closing bracket with nothing to close.');
    throw fail('concat','Two sentences sit side by side with no connective between them. No clause of the definition allows that.');
  }
  return a;
}
/* Returns {ast, informal}. informal = true when only the convention of dropping
   outer parentheses makes it a sentence. Throws an Error with a reason otherwise. */
function parse(src){
  const t=tokenize(src);
  try{return{ast:strict(t),informal:false}}
  catch(e1){
    if(e1.code!=='outer') throw e1;
    try{return{ast:strict(['(',...t,')']),informal:true}}
    catch(e2){
      if(e2.code==='multi') throw fail('multi','Each binary connective needs its own pair of brackets, so two binary connectives can\'t share one level. Add brackets to show the grouping, for example (A & B) & C.');
      throw e2;
    }
  }
}

function show(n){
  if(n.v) return n.v;
  if(n.op==='~') return '~ '+show(n.a);
  const [o,c]=n.br==='['?['[',']']:['(',')'];
  return o+show(n.l)+' '+n.op+' '+show(n.r)+c;
}
/* Display a whole sentence with its outermost brackets dropped. */
function showTop(n){const s=show(n);return n.op&&n.op!=='~'?s.slice(1,-1):s}
function kind(n){return n.v?'Atomic sentence':KIND[n.op]}
function immediate(n){return n.v?[]:n.a?[n.a]:[n.l,n.r]}
/* Components in the book's order: the sentence, its immediate components, theirs, ... */
function components(n){
  const out=[],seen=new Set(),q=[n];
  while(q.length){const x=q.shift(),k=show(x);if(!seen.has(k)){seen.add(k);out.push(x)}q.push(...immediate(x))}
  return out;
}
/* Bottom-up construction, citing clauses 1–6 of the recursive definition. */
function buildSteps(n){
  const out=[],seen=new Set();
  (function walk(x){
    immediate(x).forEach(walk);
    const k=show(x);if(seen.has(k))return;seen.add(k);
    out.push({s:k,clause:x.v?1:CLAUSE[x.op]});
  })(n);
  return out;
}
function ev(n,env){
  if(n.v) return env[n.v];
  switch(n.op){
    case '~':return !ev(n.a,env);
    case '&':return ev(n.l,env)&&ev(n.r,env);
    case '∨':return ev(n.l,env)||ev(n.r,env);
    case '⊃':return !ev(n.l,env)||ev(n.r,env);
    case '≡':return ev(n.l,env)===ev(n.r,env);
  }
}
function letters(n,set=new Set()){if(n.v)set.add(n.v);else immediate(n).forEach(c=>letters(c,set));return set}
/* The book's extended alphabetical order (3.1): unsubscripted letters first, then those with subscript 1, and so on. */
const sortLetters=a=>a.sort((x,y)=>{const sx=+x.slice(1)||0,sy=+y.slice(1)||0;return sx!==sy?sx-sy:x[0]<y[0]?-1:x[0]>y[0]?1:0});
/* Joint truth-table for several sentences. Returns {asts, vs, rows:[{env, vals}]};
   throws an Error whose .index says which sentence failed to parse. */
function joint(srcs,maxLetters=6){
  const asts=srcs.map((s,i)=>{try{return parse(s).ast}catch(e){e.index=i;throw e}});
  const set=new Set();asts.forEach(a=>letters(a,set));
  const vs=sortLetters([...set]);
  if(vs.length>maxLetters){const e=new Error('These sentences use '+vs.length+' sentence letters ('+(1<<vs.length)+' rows). Keep it to '+maxLetters+' or fewer.');e.index=-1;throw e}
  return{asts,vs,rows:rows(vs).map(env=>({env,vals:asts.map(a=>ev(a,env))}))};
}
function rows(vs){
  const out=[],n=vs.length;
  for(let i=0;i<(1<<n);i++){const env={};vs.forEach((v,j)=>env[v]=!((i>>(n-1-j))&1));out.push(env)}
  return out;
}
const tv=b=>'<span class="'+(b?'T':'F')+'">'+(b?'T':'F')+'</span>';

/* Formula input: symbol buttons insert at the cursor, typed shortcuts become book symbols. */
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
const KEYS_HTML='<div class="keys" aria-label="Insert a symbol">'+
  [['~ ','Tilde (type ~ or !)','~'],[' & ','Ampersand (type &)','&'],[' ∨ ','Wedge (type v or |)','∨'],[' ⊃ ','Horseshoe (type > or ->)','⊃'],[' ≡ ','Triple bar (type = or <->)','≡'],['(','Open parenthesis','('],[')','Close parenthesis',')'],['[','Open bracket','['],[']','Close bracket',']']]
  .map(k=>'<button type="button" class="key" data-ins="'+k[0]+'" title="'+esc(k[1])+'">'+k[2]+'</button>').join('')+'</div>';

/* Truth-table builder (section 3.1 style), used on the home page. */
function truthTable(inp,tt,st){
  let res;
  try{res=parse(inp.value)}catch(e){st.innerHTML='<span class="err">'+esc(e.message)+'</span>';tt.innerHTML='';return}
  const ast=res.ast,vs=sortLetters([...letters(ast)]);
  if(vs.length>6){st.innerHTML='<span class="err">That uses '+vs.length+' sentence letters ('+(1<<vs.length)+' rows). Keep it to 6 or fewer.</span>';tt.innerHTML='';return}
  const cols=buildSteps(ast).filter(s=>s.clause>1).map(s=>parse(s.s).ast),R=rows(vs);
  let h='<thead><tr>'+vs.map((v,i)=>'<th class="'+(i===vs.length-1?'v':'')+'">'+v+'</th>').join('');
  h+=cols.map((c,i)=>'<th class="'+(i===cols.length-1?'main':'')+'">'+esc(showTop(c))+'</th>').join('')+'</tr></thead><tbody>';
  let t=0;
  R.forEach(env=>{
    if(ev(ast,env))t++;
    h+='<tr>'+vs.map((v,i)=>'<td class="'+(i===vs.length-1?'v':'')+'">'+tv(env[v])+'</td>').join('');
    h+=cols.map((c,i)=>'<td class="'+(i===cols.length-1?'main':'')+'">'+tv(ev(c,env))+'</td>').join('')+'</tr>';
  });
  tt.innerHTML=h+'</tbody>';
  const k=t===R.length?['good','Truth-functionally true','true on every row']:t===0?['bad','Truth-functionally false','false on every row']:['mid','Truth-functionally indeterminate','true on '+t+' of '+R.length+' rows'];
  st.innerHTML='<span class="pill '+k[0]+'">'+k[1]+'</span><span class="note">The main connective column is '+k[2]+'.'+(res.informal?' Outer parentheses dropped.':'')+'</span>';
}

/* Multiple-choice quiz with per-viewer progress. render(q, answer) returns the question body;
   options are buttons carrying data-pick; q.correct holds the right pick as a string. */
function quiz(el,items,key,render){
  let state=store.get(key,{i:0,ans:{}});
  if(!(state.i<items.length)) state={i:0,ans:{}};
  const draw=()=>{
    const q=items[state.i],a=state.ans[state.i];
    const done=Object.keys(state.ans).length,right=Object.values(state.ans).filter(x=>x.ok).length;
    el.innerHTML='<div class="qcard"><div class="qtop"><span class="qnum">Question '+(state.i+1)+' of '+items.length+'</span><span class="score">'+right+' / '+done+' correct</span></div>'+render(q,a)+
      '<div class="qnav"><button type="button" class="btn ghost" data-nav="-1"'+(state.i===0?' disabled':'')+'>Previous</button><button type="button" class="btn" data-nav="1">'+(state.i===items.length-1?'Back to first':'Next question')+'</button>'+(done?'<button type="button" class="btn ghost" data-reset>Reset this set</button>':'')+'</div></div>';
  };
  el.addEventListener('click',e=>{
    const b=e.target.closest('button');if(!b)return;
    if(b.dataset.nav) state.i=(state.i+Number(b.dataset.nav)+items.length)%items.length;
    else if(b.hasAttribute('data-reset')) state={i:0,ans:{}};
    else if(b.dataset.pick!==undefined&&!state.ans[state.i]){const q=items[state.i];state.ans[state.i]={pick:b.dataset.pick,ok:b.dataset.pick===String(q.correct)}}
    else return;
    store.set(key,state);draw();
  });
  draw();
}
/* Option buttons for a quiz question. opts: [{v, label}] */
function options(opts,q,a,cls){
  return '<div class="opts">'+opts.map(o=>{
    const v=String(o.v);let c='opt'+(cls?' '+cls:'');
    if(a){if(v===String(q.correct))c+=' right';else if(v===a.pick)c+=' wrong'}
    return '<button type="button" class="'+c+'" data-pick="'+esc(v)+'"'+(a?' disabled':'')+'>'+esc(o.label)+'</button>';
  }).join('')+'</div>';
}

/* Common quiz shape: items {s or html, k (key lines), correct, why}; opts is a list of
   {v,label} or a function of the item. word=true sets labels in the display face. */
function mcQuiz(el,items,key,opts,word){
  quiz(el,items,key,(q,a)=>{
    const o=typeof opts==='function'?opts(q):opts;
    const right=o.find(x=>String(x.v)===String(q.correct));
    return '<div class="qtext">'+(q.html||esc(q.s))+'</div>'+
      (q.k?'<div class="key-legend">'+q.k.map(k=>'<span class="f">'+esc(k)+'</span>').join('')+'</div>':'')+
      options(o,q,a,word?'word':'')+
      (a?'<div class="feedback '+(a.ok?'good':'bad')+'"><b>'+(a.ok?'Correct.':'Not quite. The answer is: '+esc(right?right.label:q.correct)+'.')+'</b><span>'+(q.whyHtml||esc(q.why))+'</span></div>':'');
  });
}

function tabs(bar,key){
  const btns=[...bar.querySelectorAll('.tab')];
  const show=p=>btns.forEach(b=>{const on=b.dataset.p===p;b.setAttribute('aria-selected',on);document.getElementById(b.dataset.p).hidden=!on});
  btns.forEach(b=>b.addEventListener('click',()=>{show(b.dataset.p);store.set(key,b.dataset.p)}));
  const saved=store.get(key,null);if(saved&&btns.some(b=>b.dataset.p===saved))show(saved);
}

window.SL={joint,sortLetters,tv,parse,show,showTop,kind,immediate,components,buildSteps,ev,letters,rows,normalize,esc,store,wireInput,KEYS_HTML,truthTable,quiz,mcQuiz,options,tabs,NAME,KIND};
})();

/* Open every page at the top, unless the link points at a section (#s21 and so on).
   Browsers and the artifact viewer may otherwise restore the previous scroll position. */
(function(){
  try{history.scrollRestoration='manual'}catch(e){}
  function toTop(){
    const target=location.hash&&document.getElementById(location.hash.slice(1));
    const root=document.documentElement,prev=root.style.scrollBehavior;
    root.style.scrollBehavior='auto';
    if(target){target.scrollIntoView({block:'start'});root.style.scrollBehavior=prev;return}
    window.scrollTo(0,0);
    /* also bring the top of the page into view if the viewer scrolls an outer frame */
    try{document.body.scrollIntoView({block:'start',behavior:'auto'})}catch(e){}
    root.style.scrollBehavior=prev;
  }
  toTop();
  window.addEventListener('load',toTop);
  window.addEventListener('pageshow',e=>{if(e.persisted)toTop()});
})();
