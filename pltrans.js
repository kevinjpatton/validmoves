/* Valid Moves: translation problems for PL and PLE (The Logic Book 7.3–7.5).
   English sentences about people are built from patterns with a symbolization key
   (UD: people). Answers are compared with the model symbolization on every interpretation
   whose UD has 1, 2 or 3 members; an answer that agrees on all of them is accepted. PL has
   no decision procedure, so this is a strong practical check rather than a proof, and the
   page says so. Patterns list common mistakes so feedback can name them.
   Requires logic.js and pl.js. */
(function(){
const {parse,showTop,evaluate,findModel,describe,isSentence,vocab}=PL;
function rng(seed){let a=seed>>>0;return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}

const NOUNS=[
  {L:'S',sg:'student',pl:'students',def:'x is a student'},
  {L:'T',sg:'teacher',pl:'teachers',def:'x is a teacher'},
  {L:'M',sg:'musician',pl:'musicians',def:'x is a musician'},
  {L:'D',sg:'doctor',pl:'doctors',def:'x is a doctor'},
  {L:'W',sg:'writer',pl:'writers',def:'x is a writer'},
  {L:'A',sg:'athlete',pl:'athletes',def:'x is an athlete'}
];
const VERBS=[
  {L:'P',s3:'passes',pl:'pass',neg3:'doesn\'t pass',negpl:'don\'t pass',def:'x passes'},
  {L:'V',s3:'votes',pl:'vote',neg3:'doesn\'t vote',negpl:'don\'t vote',def:'x votes'},
  {L:'C',s3:'cooks',pl:'cook',neg3:'doesn\'t cook',negpl:'don\'t cook',def:'x cooks'},
  {L:'J',s3:'jogs',pl:'jog',neg3:'doesn\'t jog',negpl:'don\'t jog',def:'x jogs'},
  {L:'G',s3:'gardens',pl:'garden',neg3:'doesn\'t garden',negpl:'don\'t garden',def:'x gardens'},
  {L:'B',s3:'blogs',pl:'blog',neg3:'doesn\'t blog',negpl:'don\'t blog',def:'x blogs'}
];
const RELS=[
  {L:'L',s3:'likes',pl:'like',def:'x likes y'},
  {L:'H',s3:'helps',pl:'help',def:'x helps y'},
  {L:'K',s3:'knows',pl:'know',def:'x knows y'},
  {L:'R',s3:'respects',pl:'respect',def:'x respects y'},
  {L:'F',s3:'follows',pl:'follow',def:'x follows y'}
];
const NAMES=[{c:'a',n:'Ada'},{c:'b',n:'Ben'},{c:'c',n:'Cara'},{c:'e',n:'Eli'},{c:'g',n:'Gia'},{c:'k',n:'Kai'},{c:'n',n:'Nora'},{c:'s',n:'Sam'}];
const cap=s=>s.charAt(0).toUpperCase()+s.slice(1);

/* Patterns. e(n,o,v,w,r,a) gives the English. The model answer and mistakes are written
   with N, O (nouns), V, W (verbs), R (relation) and the constant a; these are replaced by
   the problem's letters. Hints and messages may use {n} {ns} {o} {v} {w} {r} {a} for words.
   ok: other correct forms (checked in tests). */
const T=[
  /* ---------- warm-up: one quantifier ---------- */
  {lv:1,e:(n,o,v)=>'all '+n.pl+' '+v.pl,a:'(∀x)(Nx ⊃ Vx)',m:[['(∀x)(Nx & Vx)','With & this says everyone is a {n} and {v}. Universal claims pair with ⊃.'],['(∃x)(Nx & Vx)','That only says some {ns} {vp}. "All" is universal.']],h:'Universal claims pair with ⊃: each x is such that if x is a {n}, then x {v}.'},
  {lv:1,e:(n,o,v)=>'every '+n.sg+' '+v.s3,a:'(∀x)(Nx ⊃ Vx)',m:[['(∀x)(Nx & Vx)','With & this says everyone is a {n} and {v}. Universal claims pair with ⊃.']],h:'"Every" is universal; pair it with ⊃.'},
  {lv:1,e:(n,o,v)=>'some '+n.pl+' '+v.pl,a:'(∃x)(Nx & Vx)',m:[['(∃x)(Nx ⊃ Vx)','With ⊃ this is true as soon as anyone isn\'t a {n}. Existential claims pair with &.']],h:'Existential claims pair with &: there is an x that is a {n} and {v}.'},
  {lv:1,e:(n,o,v)=>'no '+n.sg+' '+v.s3,a:'(∀x)(Nx ⊃ ~ Vx)',ok:['~ (∃x)(Nx & Vx)'],m:[['~ (∀x)(Nx ⊃ Vx)','That says "not all {ns} {vp}". "No" says none do.'],['(∃x)(Nx & ~ Vx)','That says some {n} doesn\'t. "No" says none do.']],h:'"No {n} {v}": each {n} fails to, or equivalently, there is no {n} who does.'},
  {lv:1,e:(n,o,v)=>'not all '+n.pl+' '+v.pl,a:'~ (∀x)(Nx ⊃ Vx)',ok:['(∃x)(Nx & ~ Vx)'],m:[['(∀x)(Nx ⊃ ~ Vx)','That says no {n} {v}. "Not all" only denies the universal claim.']],h:'Negate the whole universal sentence, or say that some {n} doesn\'t.'},
  {lv:1,e:(n,o,v)=>'some '+n.pl+' '+v.negpl,a:'(∃x)(Nx & ~ Vx)',ok:['~ (∀x)(Nx ⊃ Vx)'],m:[['~ (∃x)(Nx & Vx)','That says no {n} does. The sentence only says some don\'t.']],h:'Existential, with a negated predicate.'},
  {lv:1,e:(n,o,v)=>'only '+n.pl+' '+v.pl,a:'(∀x)(Vx ⊃ Nx)',m:[['(∀x)(Nx ⊃ Vx)','Reversed. "Only {ns} {vp}" says anyone who {v} is a {n}.']],h:'"Only": if someone {v}, then they are a {n}.'},
  {lv:1,e:(n,o,v)=>'everyone '+v.s3,a:'(∀x)Vx',h:'The UD is people, so "everyone" needs no extra predicate.'},
  {lv:1,e:(n,o,v)=>'someone '+v.neg3,a:'(∃x)~ Vx',ok:['~ (∀x)Vx'],m:[['~ (∃x)Vx','That says no one {v}. "Someone doesn\'t" is weaker.']],h:'There is an x such that x doesn\'t: the tilde goes inside the existential.'},
  {lv:1,e:(n,o,v)=>'no one '+v.s3,a:'~ (∃x)Vx',ok:['(∀x)~ Vx'],m:[['(∃x)~ Vx','That says someone doesn\'t. "No one" says nobody does.']],h:'There is no x such that x {v}.'},
  {lv:1,e:(n,o,v,w,r,a)=>a.n+' is a '+n.sg+' who '+v.neg3,a:'Na & ~ Va',h:'No quantifier needed: two atomic sentences about {a}.'},
  /* ---------- standard: two predicates, or a relation with a name ---------- */
  {lv:2,e:(n,o,v,w)=>'every '+n.sg+' who '+v.s3+' '+w.s3,a:'(∀x)((Nx & Vx) ⊃ Wx)',ok:['(∀x)(Nx ⊃ (Vx ⊃ Wx))'],m:[['(∀x)((Nx & Vx) & Wx)','Universal claims pair with ⊃.'],['(∀x)(Nx ⊃ Wx)','The "who" clause narrows down which {ns}: put it in the antecedent.']],h:'The "who" clause joins the antecedent: if x is a {n} and x {v}, then x {w}.'},
  {lv:2,e:(n,o,v,w)=>'some '+n.pl+' who '+v.pl+' '+w.negpl,a:'(∃x)((Nx & Vx) & ~ Wx)',h:'Existential: someone is a {n}, {v}, and doesn\'t {wb}.'},
  {lv:2,e:(n,o,v,w,r,a)=>a.n+' '+r.s3+' every '+n.sg,a:'(∀x)(Nx ⊃ Rax)',m:[['(∀x)(Nx & Rax)','Universal claims pair with ⊃.'],['(∀x)(Nx ⊃ Rxa)','Term order matters: {a} is the one who {r}, so {a}\'s constant comes first.']],h:'Each x is such that if x is a {n}, then {a} {r} x.'},
  {lv:2,e:(n,o,v,w,r,a)=>'every '+n.sg+' '+r.s3+' '+a.n,a:'(∀x)(Nx ⊃ Rxa)',m:[['(∀x)(Nx ⊃ Rax)','Term order matters: here each {n} {r} {a}, so x comes first.']],h:'Each x is such that if x is a {n}, then x {r} {a}.'},
  {lv:2,e:(n,o,v,w,r,a)=>a.n+' '+r.s3+' some '+n.sg,a:'(∃x)(Nx & Rax)',m:[['(∃x)(Nx ⊃ Rax)','Existential claims pair with &.']],h:'There is an x that is a {n} and that {a} {r}.'},
  {lv:2,e:(n,o,v,w,r,a)=>'no one '+r.s3+' '+a.n,a:'~ (∃x)Rxa',ok:['(∀x)~ Rxa'],m:[['~ (∃x)Rax','Term order: nobody {r} {a}, so x comes first.']],h:'There is no x such that x {r} {a}.'},
  {lv:2,e:(n,o,v,w,r,a)=>'if any '+n.sg+' '+v.s3+', then '+a.n+' '+w.s3,a:'(∀x)((Nx & Vx) ⊃ Wa)',ok:['(∃x)(Nx & Vx) ⊃ Wa'],m:[['(∀x)(Nx ⊃ Vx) ⊃ Wa','That reads "any" as "every". Here "any" means "if even one".']],h:'"If any … then": if there is at least one, the consequent follows.'},
  {lv:2,e:(n,o,v,w,r,a)=>'if every '+n.sg+' '+v.s3+', then '+a.n+' '+w.s3,a:'(∀x)(Nx ⊃ Vx) ⊃ Wa',m:[['(∃x)(Nx & Vx) ⊃ Wa','That says "if any". This sentence needs all of them.']],h:'The antecedent is a whole universal sentence.'},
  {lv:2,e:(n,o,v)=>'all '+n.pl+' and '+o.pl+' '+v.pl,a:'(∀x)((Nx ∨ Ox) ⊃ Vx)',ok:['(∀x)(Nx ⊃ Vx) & (∀x)(Ox ⊃ Vx)'],m:[['(∀x)((Nx & Ox) ⊃ Vx)','That only covers people who are both a {n} and a {o}. The sentence is about each group: use ∨, or two universal sentences.']],h:'Careful with "and": anyone in either group {v}.'},
  /* ---------- challenge: overlapping quantifiers and identity ---------- */
  {lv:3,e:(n,o,v,w,r)=>'everyone '+r.s3+' someone',a:'(∀x)(∃y)Rxy',m:[['(∃y)(∀x)Rxy','Quantifier order: that says there is one person whom everyone {r}.'],['(∃x)(∀y)Rxy','That says someone {r} everyone.']],h:'Each x has some y or other: the universal comes first.'},
  {lv:3,e:(n,o,v,w,r)=>'someone '+r.s3+' everyone',a:'(∃x)(∀y)Rxy',m:[['(∀y)(∃x)Rxy','Quantifier order: that only says everyone is reached by someone or other.']],h:'One x who {r} every y: the existential comes first.'},
  {lv:3,e:(n,o,v,w,r)=>'there is someone whom everyone '+r.s3,a:'(∃y)(∀x)Rxy',m:[['(∀x)(∃y)Rxy','Quantifier order: the sentence says there is one person whom they all {rp}.']],h:'One y such that every x {r} y.'},
  {lv:3,e:(n,o,v,w,r)=>'every '+n.sg+' '+r.s3+' some '+o.sg,a:'(∀x)(Nx ⊃ (∃y)(Oy & Rxy))',m:[['(∃y)(Oy & (∀x)(Nx ⊃ Rxy))','That says there\'s one particular {o} for all of them.']],h:'Each {n} has some {o} or other: the existential goes inside the universal.'},
  {lv:3,e:(n,o,v,w,r)=>'no '+n.sg+' '+r.s3+' every '+o.sg,a:'~ (∃x)(Nx & (∀y)(Oy ⊃ Rxy))',ok:['(∀x)(Nx ⊃ ~ (∀y)(Oy ⊃ Rxy))'],h:'There is no {n} who {r} every {o}.'},
  {lv:3,e:(n,o,v,w,r)=>'every '+n.sg+' '+r.s3+' every '+o.sg,a:'(∀x)(Nx ⊃ (∀y)(Oy ⊃ Rxy))',ok:['(∀x)(∀y)((Nx & Oy) ⊃ Rxy)'],h:'Two universals, each paired with ⊃.'},
  {lv:3,e:(n)=>'there are at least two '+n.pl,a:'(∃x)(∃y)((Nx & Ny) & ~ x = y)',m:[['(∃x)(∃y)(Nx & Ny)','Different variables can pick out the same person: add ~ x = y.']],h:'Two {ns} who are not identical.'},
  {lv:3,e:(n)=>'there is exactly one '+n.sg,a:'(∃x)(Nx & (∀y)(Ny ⊃ y = x))',m:[['(∃x)Nx','That says at least one. "Exactly one" also says every {n} is that one.']],h:'There is a {n}, and every {n} is identical to it.'},
  {lv:3,e:(n)=>'there is at most one '+n.sg,a:'(∀x)(∀y)((Nx & Ny) ⊃ x = y)',m:[['(∃x)(Nx & (∀y)(Ny ⊃ y = x))','That says exactly one. "At most one" is also true if there are none.']],h:'Any two {ns} are identical.'},
  {lv:3,e:(n,o,v,w,r,a)=>'everyone except '+a.n+' '+v.s3,a:'~ Va & (∀x)(~ x = a ⊃ Vx)',m:[['(∀x)(~ x = a ⊃ Vx)','"Except" also says that {a} doesn\'t.']],h:'Two parts: {a} doesn\'t, and everyone other than {a} does.'},
  {lv:3,e:(n,o,v,w,r,a)=>a.n+' is the only '+n.sg+' who '+v.s3,a:'(Na & Va) & (∀x)((Nx & Vx) ⊃ x = a)',m:[['Na & Va','That leaves out "only": any {n} who {v} must be {a}.']],h:'{a} is a {n} who {v}, and any {n} who {v} is {a}.'}
];
T.forEach((t,i)=>t.id=i);

/* replace the metavariables in a pattern formula; the only lowercase "a" in these is the constant */
function subst(s,m){
  let out='';
  for(let i=0;i<s.length;i++){
    const c=s[i];
    if('NOVWR'.includes(c))out+=m[c];
    else if(c==='a')out+=m.a;
    else out+=c;
  }
  return out;
}
function words(s,w){return s.replace(/\{(\w+)\}/g,(x,k)=>w[k]??x)}

/* quasi-English paraphrase, as in 7.3 */
function para(n,G){
  const t=x=>x.t==='con'?G.names[x.n]:x.n;
  switch(n.op){
    case 'atom':{
      if(n.pred==='=')return t(n.args[0])+' is identical to '+t(n.args[1]);
      const d=G.defs[n.pred];
      return d.replace(/\bx\b/,'\u0000').replace(/\by\b/,'\u0001').replace('\u0000',t(n.args[0])).replace('\u0001',n.args[1]?t(n.args[1]):'');
    }
    case '~':return 'it is not the case that '+para(n.a,G);
    case '∀':return 'each '+n.v+' is such that '+para(n.a,G);
    case '∃':return 'there is '+(n.v==='x'?'an ':'a ')+n.v+' such that '+para(n.a,G);
    case '&':return '('+para(n.l,G)+' and '+para(n.r,G)+')';
    case '∨':return '(either '+para(n.l,G)+' or '+para(n.r,G)+')';
    case '⊃':return '(if '+para(n.l,G)+' then '+para(n.r,G)+')';
    case '≡':return '('+para(n.l,G)+' if and only if '+para(n.r,G)+')';
  }
}
const stripOuter=s=>s.startsWith('(')&&s.endsWith(')')?s.slice(1,-1):s;

function generate(opts){
  const seed=opts.seed>>>0,level=opts.level||1;
  const r=rng(seed),pick=a=>a[Math.floor(r()*a.length)];
  const pool=T.filter(t=>t.lv===level);
  const t=pool[Math.floor(r()*pool.length)];
  const sh=a=>[...a].sort(()=>r()-0.5);
  const ns=sh(NOUNS),vs=sh(VERBS),rel=pick(RELS),nm=pick(NAMES);
  const n1=ns[0],n2=ns[1],v1=vs[0],v2=vs[1];
  const m={N:n1.L,O:n2.L,V:v1.L,W:v2.L,R:rel.L,a:nm.c};
  const W={n:n1.sg,ns:n1.pl,o:n2.sg,v:v1.s3,vp:v1.pl,w:v2.s3,wb:v2.pl,r:rel.s3,rp:rel.pl,a:nm.n};
  const english=cap(t.e(n1,n2,v1,v2,rel,nm))+'.';
  const answer=parse(subst(t.a,m)).ast;
  const V0={preds:{},consts:new Set(),fns:{},letters:new Set()};vocab(answer,V0);
  const defs={},names={};
  [n1,n2,v1,v2].forEach(x=>defs[x.L]=x.def);defs[rel.L]=rel.def;names[nm.c]=nm.n;
  const key=['UD: people',...Object.keys(V0.preds).sort().map(p=>p+(V0.preds[p]===2?'xy':'x')+': '+defs[p]),...[...V0.consts].map(c=>c+': '+names[c])];
  return{pattern:t.id,level,english,answer,answerText:showTop(answer),key,vocab:V0,hint:words(t.h,W),
    mistakes:(t.m||[]).map(([s,msg])=>({ast:parse(subst(s,m)).ast,msg:words(msg,W)})),
    alts:(t.ok||[]).map(s=>parse(subst(s,m)).ast),
    paraphrase:cap(stripOuter(para(answer,{defs,names})))+'.'};
}

/* Look for an interpretation (UD of 1–3 members) on which a and b differ. */
function differ(a,b){return findModel([a,b],I=>evaluate(a,I)!==evaluate(b,I),3,3000000)}

function check(prob,text){
  let a;try{a=parse(text).ast}catch(e){return{ok:false,kind:'syntax',msg:e.message}}
  if(!isSentence(a))return{ok:false,kind:'syntax',msg:'Every variable must be bound by a quantifier: '+[...PL.freeVars(a)].join(', ')+' is free.'};
  const V={preds:{},consts:new Set(),fns:{},letters:new Set()};vocab(a,V);
  const badP=Object.keys(V.preds).filter(p=>prob.vocab.preds[p]===undefined);
  const badA=Object.keys(V.preds).filter(p=>prob.vocab.preds[p]!==undefined&&prob.vocab.preds[p]!==V.preds[p]);
  const badC=[...V.consts].filter(c=>!prob.vocab.consts.has(c));
  if(badP.length||badC.length||V.letters.size)return{ok:false,kind:'letters',msg:'Use only the predicates and names in the symbolization key. Not in the key: '+[...badP,...badC,...V.letters].join(', ')+'.'};
  if(badA.length)return{ok:false,kind:'letters',msg:badA.map(p=>p+' takes '+prob.vocab.preds[p]+' term'+(prob.vocab.preds[p]>1?'s':'')).join('; ')+'.'};
  const d=differ(a,prob.answer);
  if(d&&d.tooBig)return{ok:false,kind:'big',msg:'That sentence uses too much vocabulary to check here.'};
  if(!d)return{ok:true,msg:PL.key(a)===PL.key(prob.answer)?'Correct.':'Correct. It agrees with the model answer, '+prob.answerText+', on every small interpretation.'};
  const mk=prob.mistakes.find(mm=>!differ(a,mm.ast));
  const yours=evaluate(a,d.I);
  return{ok:false,kind:mk?'mistake':'differs',msg:mk?mk.msg:'Not equivalent to the English.',
    model:describe(d.I,d.V),yours,
    row:'On this interpretation your sentence is '+(yours?'true':'false')+' but the English sentence is '+(yours?'false':'true')+':'};
}
function encode(o){return 'P'+o.level+'-'+(o.seed>>>0).toString(36)}
function decode(s){const m=String(s).trim().match(/^P([123])-([0-9a-z]+)$/i);return m?{level:+m[1],seed:parseInt(m[2],36)>>>0}:null}
window.PLT={generate,check,encode,decode,PATTERNS:T,differ,subst};
})();
