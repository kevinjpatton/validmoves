/* Valid Moves: translation (symbolization) problems for SL, following The Logic Book 2.2–2.3.
   An English sentence is built from a pattern and a few atomic sentences ("Ada passes the
   exam"), with a symbolization key. Answers are checked for truth-functional equivalence with
   the model symbolization, so any correct symbolization is accepted. Patterns list common
   mistakes so feedback can name them. Seeded: a code always rebuilds the same sentence.
   Requires logic.js. */
(function(){
const {show,showTop,parse,joint}=SL;
const N=a=>({op:'~',a}),B=(op,l,r)=>({op,l,r}),V=v=>({v});
const AND=(a,b)=>B('&',a,b),OR=(a,b)=>B('∨',a,b),IF=(a,b)=>B('⊃',a,b),IFF=(a,b)=>B('≡',a,b);
function rng(seed){let a=seed>>>0;return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}

/* Subjects have distinct initials, which become the sentence letters. */
const SUBJECTS=['Ada','Ben','Cara','Dev','Eli','Finn','Gia','Hugo','Iris','Jon','Kai','Lena','Max','Nora','Omar','Priya','Rosa','Sam','Tess','Uma','Vic','Will','Yuki','Zoe'];
/* Predicates: third-person singular, its negation, and the plain form used after "both" or "don't". */
const PREDS=[
  {pos:'passes the exam',neg:'doesn\'t pass the exam',base:'pass the exam'},
  {pos:'comes to the party',neg:'doesn\'t come to the party',base:'come to the party'},
  {pos:'plays in the match',neg:'doesn\'t play in the match',base:'play in the match'},
  {pos:'sings in the concert',neg:'doesn\'t sing in the concert',base:'sing in the concert'},
  {pos:'finishes the reading',neg:'doesn\'t finish the reading',base:'finish the reading'},
  {pos:'gets the job',neg:'doesn\'t get the job',base:'get the job'},
  {pos:'wins the race',neg:'doesn\'t win the race',base:'win the race'},
  {pos:'votes',neg:'doesn\'t vote',base:'vote'},
  {pos:'joins the trip',neg:'doesn\'t join the trip',base:'join the trip'},
  {pos:'brings dessert',neg:'doesn\'t bring dessert',base:'bring dessert'},
  {pos:'is elected',neg:'isn\'t elected',base:'be elected',be:true},
  {pos:'is late',neg:'isn\'t late',base:'be late',be:true}
];
const cap=s=>s.replace(/^(\(?)(.)/,(m,a,b)=>a+b.toUpperCase());

/* Patterns. shared: P and Q have the same predicate (needed for "neither Ada nor Ben ...").
   e: English, given atoms p, q, r ({s: subject, pos, neg, base}) and the predicate of p.
   a: model symbolization.  m: common mistakes [symbolization, message].  h: hint. */
const T=[
  /* ---------- warm-up: one connective, or one plus a negation ---------- */
  {lv:1,e:(p)=>p.neg,a:(P)=>N(P),h:'"Doesn\'t" is a negation.'},
  {lv:1,e:(p,q)=>p.pos+' and '+q.pos,a:(P,Q)=>AND(P,Q),h:'"And" joins two complete sentences.'},
  {lv:1,e:(p,q)=>p.pos+', but '+q.neg,a:(P,Q)=>AND(P,N(Q)),h:'"But" works like "and"; the contrast it suggests drops out.'},
  {lv:1,e:(p,q)=>'although '+p.pos+', '+q.pos,a:(P,Q)=>AND(P,Q),h:'"Although" asserts both parts, so it is a conjunction.'},
  {lv:1,e:(p,q)=>'either '+p.pos+' or '+q.pos,a:(P,Q)=>OR(P,Q),h:'"Either … or" is a disjunction.'},
  {lv:1,e:(p,q)=>p.pos+' unless '+q.pos,a:(P,Q)=>OR(P,Q),m:[[(P,Q)=>AND(P,N(Q)),'"Unless" is symbolized as "or" in the book, not "and not".'],[(P,Q)=>IF(Q,N(P)),'That reads "unless" as "if … then not". The book treats "p unless q" as p ∨ q.']],h:'The book symbolizes "p unless q" as p ∨ q (equivalently ~ q ⊃ p).'},
  {lv:1,e:(p,q)=>'if '+p.pos+', then '+q.pos,a:(P,Q)=>IF(P,Q),m:[[(P,Q)=>IF(Q,P),'The conditional is reversed: the "if" clause is the antecedent.']],h:'The "if" clause is the antecedent.'},
  {lv:1,e:(p,q)=>q.pos+' if '+p.pos,a:(P,Q)=>IF(P,Q),m:[[(P,Q)=>IF(Q,P),'Reversed. "q if p" means if p then q: whatever follows "if" is the antecedent, wherever it sits.']],h:'Whatever follows "if" is the antecedent, even at the end of the sentence.'},
  {lv:1,e:(p,q)=>p.pos+' only if '+q.pos,a:(P,Q)=>IF(P,Q),m:[[(P,Q)=>IF(Q,P),'Reversed. "Only if" introduces the consequent: "p only if q" means if p then q.'],[(P,Q)=>IFF(P,Q),'"Only if" gives one direction, not a biconditional.']],h:'"Only if" introduces the consequent (a necessary condition).'},
  {lv:1,e:(p,q)=>q.pos+' provided that '+p.pos,a:(P,Q)=>IF(P,Q),m:[[(P,Q)=>IF(Q,P),'Reversed. "Provided that" works like "if": it introduces the antecedent.']],h:'"Provided that" works like "if".'},
  {lv:1,e:(p,q)=>p.pos+' if and only if '+q.pos,a:(P,Q)=>IFF(P,Q),m:[[(P,Q)=>IF(P,Q),'Only half of it: "if and only if" is a biconditional.'],[(P,Q)=>IF(Q,P),'Only half of it: "if and only if" is a biconditional.']],h:'"If and only if" is the triple bar.'},
  {lv:1,e:(p,q)=>p.pos+' just in case '+q.pos,a:(P,Q)=>IFF(P,Q),m:[[(P,Q)=>IF(Q,P),'Here "just in case" means "if and only if", so it needs ≡.'],[(P,Q)=>IF(P,Q),'Here "just in case" means "if and only if", so it needs ≡.']],h:'Here "just in case" means "if and only if" (not "as a precaution").'},
  {lv:1,shared:true,e:(p,q,r,pr)=>'neither '+p.s+' nor '+q.s+' '+pr.pos,a:(P,Q)=>N(OR(P,Q)),m:[[(P,Q)=>N(AND(P,Q)),'That says "not both". "Neither … nor" says that both are false.'],[(P,Q)=>OR(N(P),N(Q)),'That says "at least one doesn\'t". "Neither … nor" says both don\'t.']],h:'"Neither … nor" denies both: ~ (p ∨ q), or equivalently ~ p & ~ q.'},
  {lv:1,shared:true,e:(p,q,r,pr)=>p.s+' and '+q.s+' don\'t both '+pr.base,a:(P,Q)=>N(AND(P,Q)),m:[[(P,Q)=>AND(N(P),N(Q)),'That says neither does. "Not both" allows one of them to.'],[(P,Q)=>N(OR(P,Q)),'That says neither does. "Not both" allows one of them to.']],h:'"Not both" negates a conjunction.'},
  {lv:1,shared:true,e:(p,q,r,pr)=>'both '+p.s+' and '+q.s+' '+pr.base,a:(P,Q)=>AND(P,Q),h:'One predicate, two subjects: two atomic sentences joined by "and".'},
  /* ---------- standard: two connectives ---------- */
  {lv:2,e:(p,q,r)=>'if '+p.pos+' and '+q.pos+', then '+r.pos,a:(P,Q,R)=>IF(AND(P,Q),R),m:[[(P,Q,R)=>AND(P,IF(Q,R)),'The main connective is "if … then": the antecedent is the whole conjunction.']],h:'The main connective is "if … then"; its antecedent is a conjunction.'},
  {lv:2,e:(p,q,r)=>'if '+p.pos+', then either '+q.pos+' or '+r.pos,a:(P,Q,R)=>IF(P,OR(Q,R)),h:'"Either" marks where the consequent\'s disjunction begins.'},
  {lv:2,e:(p,q,r)=>p.pos+' only if both '+q.pos+' and '+r.pos,a:(P,Q,R)=>IF(P,AND(Q,R)),m:[[(P,Q,R)=>IF(AND(Q,R),P),'Reversed. "Only if" introduces the consequent.']],h:'"Only if" introduces the consequent, here a conjunction.'},
  {lv:2,shared:true,e:(p,q,r,pr)=>'either '+p.s+' or '+q.s+' '+pr.pos+', but not both',a:(P,Q)=>AND(OR(P,Q),N(AND(P,Q))),m:[[(P,Q)=>OR(P,Q),'"But not both" rules out the case where both are true: the exclusive sense of "or".']],h:'"But not both" means the exclusive or: (p ∨ q) & ~ (p & q).'},
  {lv:2,e:(p,q)=>p.pos+' if and only if '+q.neg,a:(P,Q)=>IFF(P,N(Q)),m:[[(P,Q)=>IFF(P,Q),'The second side is negated: "doesn\'t" belongs inside the biconditional.']],h:'A biconditional with one side negated.'},
  {lv:2,e:(p,q)=>'if '+p.neg+', then '+q.pos,a:(P,Q)=>IF(N(P),Q),m:[[(P,Q)=>N(IF(P,Q)),'The negation belongs to the antecedent only.']],h:'The negation applies to the antecedent only.'},
  {lv:2,e:(p,q)=>p.neg+' unless '+q.pos,a:(P,Q)=>OR(N(P),Q),h:'"Unless" is a disjunction; one disjunct is a negation.'},
  {lv:2,e:(p,q,r)=>r.pos+' if either '+p.pos+' or '+q.pos,a:(P,Q,R)=>IF(OR(P,Q),R),m:[[(P,Q,R)=>IF(R,OR(P,Q)),'Reversed: what follows "if" is the antecedent.']],h:'What follows "if" is the antecedent, here a disjunction.'},
  {lv:2,e:(p,q)=>p.pos+' only if '+q.neg,a:(P,Q)=>IF(P,N(Q)),m:[[(P,Q)=>IF(N(Q),P),'Reversed: "only if" introduces the consequent.']],h:'"Only if" introduces the consequent, here a negation.'},
  {lv:2,shared:true,e:(p,q,r,pr)=>'neither '+p.s+' nor '+q.s+' '+pr.pos+', but '+r.pos,a:(P,Q,R)=>AND(N(OR(P,Q)),R),h:'"But" is the main connective; its left side is a "neither … nor".'},
  {lv:2,e:(p,q,r)=>'if '+p.pos+', then '+q.pos+'; and if '+q.pos+', then '+r.pos,a:(P,Q,R)=>AND(IF(P,Q),IF(Q,R)),m:[[(P,Q,R)=>IF(P,R),'That\'s what follows from it, not what it says: the sentence is a conjunction of two conditionals.']],h:'The semicolon and "and" join two complete conditionals.'},
  /* ---------- challenge: three connectives or tricky grouping ---------- */
  {lv:3,e:(p,q,r)=>'if '+p.pos+', then '+q.pos+' only if '+r.pos,a:(P,Q,R)=>IF(P,IF(Q,R)),m:[[(P,Q,R)=>IF(IF(P,Q),R),'The first "if … then" is the main connective; "q only if r" is its consequent.'],[(P,Q,R)=>IF(P,IF(R,Q)),'Inside the consequent, "only if" introduces the consequent: q ⊃ r.']],h:'Main connective: the first "if … then". Its consequent is "q only if r".'},
  {lv:3,e:(p,q,r)=>p.pos+' if and only if both '+q.pos+' and '+r.neg,a:(P,Q,R)=>IFF(P,AND(Q,N(R))),h:'A biconditional whose right side is a conjunction with a negated conjunct.'},
  {lv:3,shared:true,e:(p,q,r,pr)=>'either both '+p.s+' and '+q.s+' '+pr.base+', or neither does',a:(P,Q)=>OR(AND(P,Q),N(OR(P,Q))),h:'A disjunction of "both" and "neither".'},
  {lv:3,e:(p,q,r)=>'if '+p.pos+' only if '+q.pos+', then '+r.pos,a:(P,Q,R)=>IF(IF(P,Q),R),m:[[(P,Q,R)=>IF(P,IF(Q,R)),'The antecedent is the whole conditional "p only if q".']],h:'The antecedent of the main conditional is itself a conditional.'},
  {lv:3,e:(p,q,r)=>p.pos+' just in case either '+q.pos+' or '+r.pos,a:(P,Q,R)=>IFF(P,OR(Q,R)),h:'A biconditional whose right side is a disjunction.'},
  {lv:3,shared:true,e:(p,q,r,pr)=>'if neither '+p.s+' nor '+q.s+' '+pr.pos+', then '+r.pos,a:(P,Q,R)=>IF(N(OR(P,Q)),R),m:[[(P,Q,R)=>IF(N(AND(P,Q)),R),'"Neither … nor" is ~ (p ∨ q), not "not both".']],h:'The antecedent is a "neither … nor".'},
  {lv:3,e:(p,q,r)=>r.pos+' provided that '+p.pos+', unless '+q.pos,a:(P,Q,R)=>OR(IF(P,R),Q),h:'The comma before "unless" makes "unless" the main connective: (if p then r) or q.'},
  {lv:3,e:(p,q,r)=>'if '+p.pos+', then '+q.pos+' if and only if '+r.pos,a:(P,Q,R)=>IF(P,IFF(Q,R)),m:[[(P,Q,R)=>IFF(IF(P,Q),R),'The main connective is the first "if … then"; the biconditional is its consequent.']],h:'The main connective is the first "if … then".'}
];
T.forEach((t,i)=>t.id=i);

/* Paraphrase in the book's style: standard connectives, parentheses for grouping. */
function paraphrase(n,clauses,top=true){
  const wrap=s=>top?s:'('+s+')';
  if(n.v)return clauses[n.v];
  if(n.op==='~')return 'it is not the case that '+paraphrase(n.a,clauses,!(n.a.op&&n.a.op!=='~')?true:false);
  const L=paraphrase(n.l,clauses,false),R=paraphrase(n.r,clauses,false);
  if(n.op==='&')return wrap(L+' and '+R);
  if(n.op==='∨')return wrap('either '+L+' or '+R);
  if(n.op==='⊃')return wrap('if '+L+' then '+R);
  return wrap(L+' if and only if '+R);
}

function generate(opts){
  const seed=opts.seed>>>0,level=opts.level||1;
  const r=rng(seed),pick=a=>a[Math.floor(r()*a.length)];
  const pool=T.filter(t=>t.lv===level);
  const t=pool[Math.floor(r()*pool.length)];
  const subj=[...SUBJECTS].sort(()=>r()-0.5).slice(0,3);
  const prs=[...PREDS].sort(()=>r()-0.5);
  /* "both Ada and Ben …" and "don't both …" need an ordinary verb, so shared patterns skip "is …" */
  if(t.shared){const i=prs.findIndex(x=>!x.be);prs.unshift(prs.splice(i,1)[0])}
  const atoms=subj.map((s,i)=>{const pr=t.shared&&i<2?prs[0]:prs[i];return{s,letter:s[0],pos:s+' '+pr.pos,neg:s+' '+pr.neg,base:pr.base,pr}});
  const [p,q,rr]=atoms;
  const english=cap(t.e(p,q,rr,p.pr))+'.';
  const vars=atoms.map(a=>V(a.letter));
  const answer=t.a(...vars);
  const used=[...SL.letters(answer)];
  const key=atoms.filter(a=>used.includes(a.letter)).map(a=>({letter:a.letter,text:cap(a.pos)}));
  const clauses=Object.fromEntries(atoms.map(a=>[a.letter,a.pos]));
  return{pattern:t.id,level,english,answer,key,hint:t.h,mistakes:(t.m||[]).map(([f,msg])=>({ast:f(...vars),msg})),
    paraphrase:cap(paraphrase(answer,clauses))+'.'};
}

/* Check a typed symbolization. Returns {ok, msg, row} */
function check(prob,text){
  let a;try{a=parse(text).ast}catch(e){return{ok:false,kind:'syntax',msg:e.message}}
  const allowed=new Set(prob.key.map(k=>k.letter)),used=[...SL.letters(a)];
  const stray=used.filter(l=>!allowed.has(l));
  if(stray.length)return{ok:false,kind:'letters',msg:'Use only the letters in the symbolization key. '+stray.join(', ')+(stray.length>1?' aren\'t':' isn\'t')+' in it.'};
  const eqv=(x,y)=>{const J=joint([showTop(x),showTop(y)]);return J.rows.find(r=>r.vals[0]!==r.vals[1])||null};
  const diff=eqv(a,prob.answer);
  if(!diff){
    const exact=show(a).replace(/\[/g,'(').replace(/\]/g,')')===show(prob.answer);
    return{ok:true,msg:exact?'Correct.':'Correct. It\'s equivalent to the model answer, '+showTop(prob.answer)+'.'};
  }
  const m=prob.mistakes.find(m=>!eqv(a,m.ast));
  const row=prob.key.map(k=>k.letter+' = '+(diff.env[k.letter]?'T':'F')).join(', ');
  const yours=SL.ev(a,diff.env);
  return{ok:false,kind:m?'mistake':'differs',msg:m?m.msg:'Not equivalent to the English.',row:'When '+row+', your sentence is '+(yours?'true':'false')+' but the English sentence is '+(yours?'false':'true')+'.'};
}
function encode(o){return 'T'+o.level+'-'+(o.seed>>>0).toString(36)}
function decode(s){const m=String(s).trim().match(/^T([123])-([0-9a-z]+)$/i);return m?{level:+m[1],seed:parseInt(m[2],36)>>>0}:null}
window.SLT={generate,check,encode,decode,PATTERNS:T,paraphrase};
})();
