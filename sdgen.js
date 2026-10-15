/* Valid Moves: generator for SL derivation problems (SD).
   Problems come from a library of classic argument patterns, each with a model proof
   written in SD and hints. A problem fills a pattern's metavariables P, Q, R with fresh
   sentence letters, or at harder levels sometimes a short compound sentence. The filled-in
   model proof is run through derive.js and must check out before the problem is used.
   Seeded, so a problem code always rebuilds the same problem. Requires logic.js, derive.js. */
(function(){
const {show,showTop,parse}=SL;
const N=a=>({op:'~',a}),B=(op,l,r)=>({op,l,r}),V=v=>({v});
function rng(seed){let a=seed>>>0;return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const RULES=['&I','&E','∨I','∨E','⊃I','⊃E','~I','~E','≡I','≡E','R'];
const LEVELS={1:{name:'Warm-up'},2:{name:'Standard'},3:{name:'Challenge'}};

/* Each pattern: level, name, premises, goal, proof lines [depth, sentence, justification], hints.
   Depth 0 is the main scope line. Hints may mention {P}, {Q}, {R}, {S}. */
const T=[
  /* ---------- warm-up: no subderivations ---------- */
  {lv:1,name:'Modus ponens',prem:['P ⊃ Q','P'],goal:'Q',proof:[[0,'Q','1, 2 ⊃E']],
    hints:['You have a conditional and its antecedent.','⊃E gives the consequent.']},
  {lv:1,name:'A chain of conditionals',prem:['P ⊃ Q','Q ⊃ R','P'],goal:'R',proof:[[0,'Q','1, 3 ⊃E'],[0,'R','2, 4 ⊃E']],
    hints:['Work forwards: what does {P} give you with the first premise?','Two uses of ⊃E: first get {Q}, then {R}.']},
  {lv:1,name:'Commuting a conjunction',prem:['P & Q'],goal:'Q & P',proof:[[0,'P','1 &E'],[0,'Q','1 &E'],[0,'Q & P','3, 2 &I']],
    hints:['Take the conjunction apart, then put it back together in the other order.','&E twice, then &I.']},
  {lv:1,name:'Biconditional elimination',prem:['P ≡ Q','Q'],goal:'P',proof:[[0,'P','1, 2 ≡E']],
    hints:['A biconditional works in both directions.','≡E with the side you have gives the other side.']},
  {lv:1,name:'Adding a disjunct',prem:['P ⊃ Q','P'],goal:'Q ∨ R',proof:[[0,'Q','1, 2 ⊃E'],[0,'Q ∨ R','3 ∨I']],
    hints:['The conclusion is a disjunction: you only need one disjunct.','Get {Q} with ⊃E, then use ∨I.']},
  {lv:1,name:'Conjunction and conditional',prem:['P & Q','P ⊃ R'],goal:'R & Q',proof:[[0,'P','1 &E'],[0,'Q','1 &E'],[0,'R','2, 3 ⊃E'],[0,'R & Q','5, 4 &I']],
    hints:['The conclusion is a conjunction: derive each conjunct.','{Q} comes straight from the first premise; {R} needs {P} and ⊃E.']},
  {lv:1,name:'Two biconditionals',prem:['P ≡ Q','Q ≡ R','P'],goal:'R',proof:[[0,'Q','1, 3 ≡E'],[0,'R','2, 4 ≡E']],
    hints:['Pass along the chain of biconditionals.','≡E twice.']},
  {lv:1,name:'Nested conditional',prem:['P ⊃ (Q ⊃ R)','P','Q'],goal:'R',proof:[[0,'Q ⊃ R','1, 2 ⊃E'],[0,'R','4, 3 ⊃E']],
    hints:['The main connective of the first premise is the first ⊃.','⊃E with {P} gives {Q} ⊃ {R}; then ⊃E again.']},
  /* ---------- standard: one subderivation rule ---------- */
  {lv:2,name:'Hypothetical syllogism',prem:['P ⊃ Q','Q ⊃ R'],goal:'P ⊃ R',proof:[[1,'P','A / ⊃I'],[1,'Q','1, 3 ⊃E'],[1,'R','2, 4 ⊃E'],[0,'P ⊃ R','3–5 ⊃I']],
    hints:['The conclusion is a conditional: assume {P} and aim for {R}, then ⊃I.','Inside the subderivation, use ⊃E twice.']},
  {lv:2,name:'Modus tollens',prem:['P ⊃ Q','~ Q'],goal:'~ P',proof:[[1,'P','A / ~I'],[1,'Q','1, 3 ⊃E'],[1,'~ Q','2 R'],[0,'~ P','3–5 ~I']],
    hints:['The conclusion is a negation: assume {P} and look for a contradiction, then ~I.','From {P} you get {Q}, and you already have ~ {Q}.']},
  {lv:2,name:'Exportation',prem:['(P & Q) ⊃ R'],goal:'P ⊃ (Q ⊃ R)',proof:[[1,'P','A / ⊃I'],[2,'Q','A / ⊃I'],[2,'P & Q','2, 3 &I'],[2,'R','1, 4 ⊃E'],[1,'Q ⊃ R','3–5 ⊃I'],[0,'P ⊃ (Q ⊃ R)','2–6 ⊃I']],
    hints:['The conclusion is a conditional whose consequent is also a conditional: two ⊃I subderivations, one inside the other.','Assume {P}, then {Q}; with both you can build {P} & {Q}.']},
  {lv:2,name:'Importation',prem:['P ⊃ (Q ⊃ R)'],goal:'(P & Q) ⊃ R',proof:[[1,'P & Q','A / ⊃I'],[1,'P','2 &E'],[1,'Q','2 &E'],[1,'Q ⊃ R','1, 3 ⊃E'],[1,'R','5, 4 ⊃E'],[0,'(P & Q) ⊃ R','2–6 ⊃I']],
    hints:['Assume the antecedent, {P} & {Q}, and aim for {R}.','Split the conjunction, then use ⊃E twice.']},
  {lv:2,name:'Constructive dilemma',prem:['P ∨ Q','P ⊃ R','Q ⊃ R'],goal:'R',proof:[[1,'P','A / ∨E'],[1,'R','2, 4 ⊃E'],[1,'Q','A / ∨E'],[1,'R','3, 6 ⊃E'],[0,'R','1, 4–5, 6–7 ∨E']],
    hints:['Reason by cases with ∨E: show {R} follows from {P}, and also from {Q}.','Each case is one ⊃E. Remember to end the first subderivation before starting the second.']},
  {lv:2,name:'Biconditional from two conditionals',prem:['P ⊃ Q','Q ⊃ P'],goal:'P ≡ Q',proof:[[1,'P','A / ≡I'],[1,'Q','1, 3 ⊃E'],[1,'Q','A / ≡I'],[1,'P','2, 5 ⊃E'],[0,'P ≡ Q','3–4, 5–6 ≡I']],
    hints:['≡I needs two subderivations: from {P} to {Q}, and from {Q} to {P}.','Each one is a single ⊃E.']},
  {lv:2,name:'Contraposition',prem:['P ⊃ Q'],goal:'~ Q ⊃ ~ P',proof:[[1,'~ Q','A / ⊃I'],[2,'P','A / ~I'],[2,'Q','1, 3 ⊃E'],[2,'~ Q','2 R'],[1,'~ P','3–5 ~I'],[0,'~ Q ⊃ ~ P','2–6 ⊃I']],
    hints:['Assume ~ {Q} and aim for ~ {P}, then ⊃I.','To get ~ {P}, assume {P} and find a contradiction (~I).']},
  {lv:2,name:'Commuting a disjunction',prem:['P ∨ Q'],goal:'Q ∨ P',proof:[[1,'P','A / ∨E'],[1,'Q ∨ P','2 ∨I'],[1,'Q','A / ∨E'],[1,'Q ∨ P','4 ∨I'],[0,'Q ∨ P','1, 2–3, 4–5 ∨E']],
    hints:['You can\'t take a disjunction apart directly: reason by cases with ∨E.','In each case, ∨I gives {Q} ∨ {P}.']},
  {lv:2,name:'Negation elimination',prem:['~ P ⊃ Q','~ Q'],goal:'P',proof:[[1,'~ P','A / ~E'],[1,'Q','1, 3 ⊃E'],[1,'~ Q','2 R'],[0,'P','3–5 ~E']],
    hints:['Nothing gives {P} directly. Try ~E: assume ~ {P} and look for a contradiction.','~ {P} gives {Q} by ⊃E, and you have ~ {Q}.']},
  {lv:2,name:'Conditional with a conjunction',prem:['P ⊃ Q','P ⊃ R'],goal:'P ⊃ (Q & R)',proof:[[1,'P','A / ⊃I'],[1,'Q','1, 3 ⊃E'],[1,'R','2, 3 ⊃E'],[1,'Q & R','4, 5 &I'],[0,'P ⊃ (Q & R)','3–6 ⊃I']],
    hints:['Assume {P} and aim for {Q} & {R}.','Both conjuncts come from ⊃E.']},
  {lv:2,name:'One half of a biconditional',prem:['P ≡ Q'],goal:'Q ⊃ P',proof:[[1,'Q','A / ⊃I'],[1,'P','1, 2 ≡E'],[0,'Q ⊃ P','2–3 ⊃I']],
    hints:['Assume {Q} and aim for {P}.','≡E works from either side.']},
  /* ---------- challenge: several subderivations ---------- */
  {lv:3,name:'Disjunctive syllogism',prem:['P ∨ Q','~ P'],goal:'Q',proof:[[1,'P','A / ∨E'],[2,'~ Q','A / ~E'],[2,'P','3 R'],[2,'~ P','2 R'],[1,'Q','4–6 ~E'],[1,'Q','A / ∨E'],[0,'Q','1, 3–7, 8–8 ∨E']],
    hints:['SD has no disjunctive syllogism rule: use ∨E and show {Q} follows in both cases.','In the {P} case you have a contradiction with ~ {P}, so get {Q} by ~E. The {Q} case is just its assumption.']},
  {lv:3,name:'De Morgan, part 1',prem:['~ (P ∨ Q)'],goal:'~ P & ~ Q',proof:[[1,'P','A / ~I'],[1,'P ∨ Q','2 ∨I'],[1,'~ (P ∨ Q)','1 R'],[0,'~ P','2–4 ~I'],[1,'Q','A / ~I'],[1,'P ∨ Q','6 ∨I'],[1,'~ (P ∨ Q)','1 R'],[0,'~ Q','6–8 ~I'],[0,'~ P & ~ Q','5, 9 &I']],
    hints:['Derive each conjunct separately, each by ~I.','Assuming {P} lets you build {P} ∨ {Q}, which contradicts the premise.']},
  {lv:3,name:'De Morgan, part 2',prem:['~ P & ~ Q'],goal:'~ (P ∨ Q)',proof:[[0,'~ P','1 &E'],[0,'~ Q','1 &E'],[1,'P ∨ Q','A / ~I'],[2,'P','A / ∨E'],[2,'Q','A / ∨E'],[3,'~ P','A / ~E'],[3,'Q','6 R'],[3,'~ Q','3 R'],[2,'P','7–9 ~E'],[1,'P','4, 5–5, 6–10 ∨E'],[1,'~ P','2 R'],[0,'~ (P ∨ Q)','4–12 ~I']],
    hints:['Assume {P} ∨ {Q} and aim for a contradiction (~I).','Use ∨E inside to show {P} follows either way; that contradicts ~ {P}.']},
  {lv:3,name:'Negated conditional',prem:['~ (P ⊃ Q)'],goal:'P & ~ Q',proof:[[1,'~ P','A / ~E'],[2,'P','A / ⊃I'],[3,'~ Q','A / ~E'],[3,'P','3 R'],[3,'~ P','2 R'],[2,'Q','4–6 ~E'],[1,'P ⊃ Q','3–7 ⊃I'],[1,'~ (P ⊃ Q)','1 R'],[0,'P','2–9 ~E'],[1,'Q','A / ~I'],[2,'P','A / ⊃I'],[2,'Q','11 R'],[1,'P ⊃ Q','12–13 ⊃I'],[1,'~ (P ⊃ Q)','1 R'],[0,'~ Q','11–15 ~I'],[0,'P & ~ Q','10, 16 &I']],
    hints:['Derive {P} and ~ {Q} separately, each by contradiction with the premise.','In both cases the contradiction comes from deriving {P} ⊃ {Q}.']},
  {lv:3,name:'Distribution',prem:['P & (Q ∨ R)'],goal:'(P & Q) ∨ (P & R)',proof:[[0,'P','1 &E'],[0,'Q ∨ R','1 &E'],[1,'Q','A / ∨E'],[1,'P & Q','2, 4 &I'],[1,'(P & Q) ∨ (P & R)','5 ∨I'],[1,'R','A / ∨E'],[1,'P & R','2, 7 &I'],[1,'(P & Q) ∨ (P & R)','8 ∨I'],[0,'(P & Q) ∨ (P & R)','3, 4–6, 7–9 ∨E']],
    hints:['Split the premise, then reason by cases on {Q} ∨ {R}.','In each case build a conjunction with {P}, then ∨I.']},
  {lv:3,name:'Conditional from a disjunction',prem:['(P ∨ Q) ⊃ R'],goal:'(P ⊃ R) & (Q ⊃ R)',proof:[[1,'P','A / ⊃I'],[1,'P ∨ Q','2 ∨I'],[1,'R','1, 3 ⊃E'],[0,'P ⊃ R','2–4 ⊃I'],[1,'Q','A / ⊃I'],[1,'P ∨ Q','6 ∨I'],[1,'R','1, 7 ⊃E'],[0,'Q ⊃ R','6–8 ⊃I'],[0,'(P ⊃ R) & (Q ⊃ R)','5, 9 &I']],
    hints:['Derive each conditional by ⊃I, then join them with &I.','Assuming {P} (or {Q}) lets you build {P} ∨ {Q} for ⊃E.']},
  {lv:3,name:'Material implication',prem:['P ⊃ Q'],goal:'~ P ∨ Q',proof:[[1,'~ (~ P ∨ Q)','A / ~E'],[2,'P','A / ~I'],[2,'Q','1, 3 ⊃E'],[2,'~ P ∨ Q','4 ∨I'],[2,'~ (~ P ∨ Q)','2 R'],[1,'~ P','3–6 ~I'],[1,'~ P ∨ Q','7 ∨I'],[1,'~ (~ P ∨ Q)','2 R'],[0,'~ P ∨ Q','2–9 ~E']],
    hints:['A disjunction you can\'t get from either disjunct: assume its negation (~E).','Inside, show ~ {P} by ~I; then ∨I contradicts your assumption.']},
  {lv:3,name:'Negating both sides',prem:['P ≡ Q'],goal:'~ P ≡ ~ Q',proof:[[1,'~ P','A / ≡I'],[2,'Q','A / ~I'],[2,'P','1, 3 ≡E'],[2,'~ P','2 R'],[1,'~ Q','3–5 ~I'],[1,'~ Q','A / ≡I'],[2,'P','A / ~I'],[2,'Q','1, 8 ≡E'],[2,'~ Q','7 R'],[1,'~ P','8–10 ~I'],[0,'~ P ≡ ~ Q','2–6, 7–11 ≡I']],
    hints:['≡I: two subderivations, from ~ {P} to ~ {Q} and back.','Each direction is a small ~I.']},
  /* ---------- theorems (no premises) ---------- */
  {lv:1,th:true,name:'Commuting inside a conditional',prem:[],goal:'(P & Q) ⊃ (Q & P)',proof:[[1,'P & Q','A / ⊃I'],[1,'P','1 &E'],[1,'Q','1 &E'],[1,'Q & P','3, 2 &I'],[0,'(P & Q) ⊃ (Q & P)','1–4 ⊃I']],
    hints:['No premises: start by assuming the antecedent.','Inside, split the conjunction and rebuild it.']},
  {lv:1,th:true,name:'Simplification as a theorem',prem:[],goal:'(P & Q) ⊃ P',proof:[[1,'P & Q','A / ⊃I'],[1,'P','1 &E'],[0,'(P & Q) ⊃ P','1–2 ⊃I']],
    hints:['No premises: assume the antecedent.','One &E inside the subderivation.']},
  {lv:1,th:true,name:'Addition as a theorem',prem:[],goal:'P ⊃ (P ∨ Q)',proof:[[1,'P','A / ⊃I'],[1,'P ∨ Q','1 ∨I'],[0,'P ⊃ (P ∨ Q)','1–2 ⊃I']],
    hints:['Assume {P}.','One ∨I inside the subderivation.']},
  {lv:2,th:true,name:'Removing a double negation',prem:[],goal:'~ ~ P ⊃ P',proof:[[1,'~ ~ P','A / ⊃I'],[2,'~ P','A / ~E'],[2,'~ ~ P','1 R'],[1,'P','2–3 ~E'],[0,'~ ~ P ⊃ P','1–4 ⊃I']],
    hints:['Assume ~ ~ {P} and aim for {P}.','To get {P}, assume ~ {P} (~E): it contradicts what you assumed first.']},
  {lv:2,th:true,name:'Contraction',prem:[],goal:'(P ⊃ (P ⊃ Q)) ⊃ (P ⊃ Q)',proof:[[1,'P ⊃ (P ⊃ Q)','A / ⊃I'],[2,'P','A / ⊃I'],[2,'P ⊃ Q','1, 2 ⊃E'],[2,'Q','3, 2 ⊃E'],[1,'P ⊃ Q','2–4 ⊃I'],[0,'(P ⊃ (P ⊃ Q)) ⊃ (P ⊃ Q)','1–5 ⊃I']],
    hints:['Two ⊃I subderivations, one inside the other.','With {P} assumed, use ⊃E twice.']},
  {lv:2,th:true,name:'Weakening',prem:[],goal:'P ⊃ (Q ⊃ P)',proof:[[1,'P','A / ⊃I'],[2,'Q','A / ⊃I'],[2,'P','1 R'],[1,'Q ⊃ P','2–3 ⊃I'],[0,'P ⊃ (Q ⊃ P)','1–4 ⊃I']],
    hints:['Two ⊃I subderivations, one inside the other.','Inside both, {P} is still accessible: use R.']},
  {lv:2,th:true,name:'Non-contradiction',prem:[],goal:'~ (P & ~ P)',proof:[[1,'P & ~ P','A / ~I'],[1,'P','1 &E'],[1,'~ P','1 &E'],[0,'~ (P & ~ P)','1–3 ~I']],
    hints:['The theorem is a negation: assume what it negates.','The assumption hands you a contradiction directly.']},
  {lv:3,th:true,name:'Contraposition as a theorem',prem:[],goal:'(P ⊃ Q) ⊃ (~ Q ⊃ ~ P)',proof:[[1,'P ⊃ Q','A / ⊃I'],[2,'~ Q','A / ⊃I'],[3,'P','A / ~I'],[3,'Q','1, 3 ⊃E'],[3,'~ Q','2 R'],[2,'~ P','3–5 ~I'],[1,'~ Q ⊃ ~ P','2–6 ⊃I'],[0,'(P ⊃ Q) ⊃ (~ Q ⊃ ~ P)','1–7 ⊃I']],
    hints:['Three subderivations, nested: ⊃I, ⊃I, then ~I.','Assume {P} ⊃ {Q}, then ~ {Q}, then {P}.']},
  {lv:3,th:true,name:'Excluded middle',prem:[],goal:'P ∨ ~ P',proof:[[1,'~ (P ∨ ~ P)','A / ~E'],[2,'P','A / ~I'],[2,'P ∨ ~ P','2 ∨I'],[2,'~ (P ∨ ~ P)','1 R'],[1,'~ P','2–4 ~I'],[1,'P ∨ ~ P','5 ∨I'],[1,'~ (P ∨ ~ P)','1 R'],[0,'P ∨ ~ P','1–7 ~E']],
    hints:['Neither disjunct is derivable on its own: assume the negation of the whole thing (~E).','Inside, first show ~ {P} by ~I, then use ∨I.']},
  {lv:3,th:true,name:'Chaining conditionals',prem:[],goal:'((P ⊃ Q) & (Q ⊃ R)) ⊃ (P ⊃ R)',proof:[[1,'(P ⊃ Q) & (Q ⊃ R)','A / ⊃I'],[1,'P ⊃ Q','1 &E'],[1,'Q ⊃ R','1 &E'],[2,'P','A / ⊃I'],[2,'Q','2, 4 ⊃E'],[2,'R','3, 5 ⊃E'],[1,'P ⊃ R','4–6 ⊃I'],[0,'((P ⊃ Q) & (Q ⊃ R)) ⊃ (P ⊃ R)','1–7 ⊃I']],
    hints:['Assume the antecedent and split it.','Then it\'s hypothetical syllogism inside a ⊃I.']},
  {lv:3,th:true,name:'Double negation',prem:[],goal:'P ≡ ~ ~ P',proof:[[1,'P','A / ≡I'],[2,'~ P','A / ~I'],[2,'P','1 R'],[1,'~ ~ P','2–3 ~I'],[1,'~ ~ P','A / ≡I'],[2,'~ P','A / ~E'],[2,'~ ~ P','5 R'],[1,'P','6–7 ~E'],[0,'P ≡ ~ ~ P','1–4, 5–8 ≡I']],
    hints:['≡I: show each side from the other.','Both directions are a single negation rule.']}
];
/* parse every pattern once; metavariables are the sentence letters P, Q, R, S */
const META=['P','Q','R','S'];
T.forEach(t=>{
  t.premA=t.prem.map(s=>parse(s).ast);t.goalA=parse(t.goal).ast;
  t.proofA=t.proof.map(([d,s,j])=>[d,parse(s).ast,j]);
  t.rules=[...new Set(t.proof.map(p=>p[2].match(/([&∨⊃~≡][IE]|R)$/)).filter(Boolean).map(m=>m[1]))];
  const used=new Set();[t.goalA,...t.premA].forEach(a=>SL.letters(a,used));t.meta=META.filter(m=>used.has(m));
});
function subst(n,m){if(n.v)return m[n.v]||n;if(n.op==='~')return N(subst(n.a,m));return{op:n.op,l:subst(n.l,m),r:subst(n.r,m)}}

function generate(opts){
  const seed=opts.seed>>>0,level=opts.level||2,theorem=!!opts.theorem;
  const want=(opts.rules||[]).filter(r=>RULES.includes(r));
  const r=rng(seed),pick=a=>a[Math.floor(r()*a.length)];
  let pool=T.filter(t=>!!t.th===theorem&&t.lv===level);
  if(want.length){
    const hit=pool.filter(t=>want.some(w=>t.rules.includes(w)));
    if(hit.length)pool=hit;
    else{const any=T.filter(t=>!!t.th===theorem&&want.some(w=>t.rules.includes(w)));if(any.length)pool=any}
  }
  if(!pool.length)pool=T.filter(t=>!!t.th===theorem);
  for(let attempt=0;attempt<60;attempt++){
    const t=pick(pool);
    /* fresh letters; at harder levels a metavariable sometimes becomes a negation or a small compound */
    const letters=['A','B','C','D','E','F','G','H','J','K'].sort(()=>r()-0.5);
    const m={};let li=0,compound=false;
    t.meta.forEach(v=>{
      const x=r();
      if(level>=2&&x<0.15)m[v]=N(V(letters[li++]));
      else if(level>=3&&!compound&&x<0.3){m[v]=B(pick(['&','∨','⊃']),V(letters[li++]),V(letters[li++]));compound=true}
      else m[v]=V(letters[li++]);
    });
    const prem=t.premA.map(a=>subst(a,m)),goal=subst(t.goalA,m);
    const lines=[...prem.map(p=>[0,p,'Assumption']),...t.proofA.map(([d,a,j])=>[d,subst(a,m),j])];
    const text='Derive: '+showTop(goal)+'\n'+lines.map(([d,a,j])=>'| '.repeat(d+1)+showTop(a)+'    '+j).join('\n')+'\n';
    const chk=SDX.check(text,'SD');
    if(!chk.summary||!chk.summary.ok)continue;
    const fill=s=>s.replace(/\{([PQRS])\}/g,(x,k)=>m[k]?showTop(m[k]).length>1&&!m[k].v?'('+showTop(m[k])+')':showTop(m[k]):k);
    return{pattern:t.name,goal,premises:prem,solution:text,rules:t.rules,lines:lines.length,hintList:t.hints.map(fill),
      start:'Derive: '+showTop(goal)+'\n'+prem.map(p=>'| '+showTop(p)+'    Assumption').join('\n')+(prem.length?'\n':'')};
  }
  return null;
}
function hints(p){return p.hintList}
/* problem codes: level, type, rule mask and seed, e.g. 2A-1f-8kq3z */
function encode(o){const mask=RULES.reduce((m,r,i)=>m|((o.rules||[]).includes(r)?1<<i:0),0);return o.level+(o.theorem?'T':'A')+'-'+mask.toString(36)+'-'+(o.seed>>>0).toString(36)}
function decode(s){const m=String(s).trim().match(/^([123])([AT])-([0-9a-z]+)-([0-9a-z]+)$/i);if(!m)return null;
  const mask=parseInt(m[3],36);return{level:+m[1],theorem:m[2].toUpperCase()==='T',rules:RULES.filter((r,i)=>mask&(1<<i)),seed:parseInt(m[4],36)>>>0}}
window.SDGEN={generate,hints,encode,decode,RULES,LEVELS,PATTERNS:T};
})();
