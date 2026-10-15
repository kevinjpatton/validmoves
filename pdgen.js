/* Valid Moves: generator for PL derivation problems (PD, PD+, PDE; The Logic Book ch. 10).
   A library of classic quantifier and identity patterns, each with a model proof. A problem
   fills the pattern's predicate letters F, G, H (one-place) and R (two-place) and constants
   a, b, c with fresh ones; the filled-in proof must pass derive.js before it is used.
   Seeded, so a code always rebuilds the same problem. Requires logic.js, pl.js, derive.js. */
(function(){
const {parse,showTop}=PL;
function rng(seed){let a=seed>>>0;return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
const RULES=['∀E','∀I','∃E','∃I','⊃I','~I','~E','∨E','=E'];
const LEVELS={1:{name:'Warm-up'},2:{name:'Standard'},3:{name:'Challenge'}};

/* kind: A argument, T theorem, I identity (PDE). proof: [depth, sentence, justification]. */
const T=[
  /* ---------- warm-up ---------- */
  {lv:1,k:'A',name:'Universal instantiation',prem:['(∀x)(Fx ⊃ Gx)','Fa'],goal:'Ga',proof:[[0,'Fa ⊃ Ga','1 ∀E'],[0,'Ga','3, 2 ⊃E']],
    hints:['Get the instance of the universal for the name in your other premise.','∀E gives `Fa ⊃ Ga`; then ⊃E.']},
  {lv:1,k:'A',name:'Existential generalization',prem:['Fa & Ga'],goal:'(∃x)(Fx & Gx)',proof:[[0,'(∃x)(Fx & Gx)','1 ∃I']],
    hints:['The premise is already an instance of the conclusion.','One ∃I.']},
  {lv:1,k:'A',name:'Instance of a conjunction',prem:['(∀x)(Fx & Gx)'],goal:'Ga',proof:[[0,'Fa & Ga','1 ∀E'],[0,'Ga','2 &E']],
    hints:['Instantiate the universal with the name in the conclusion.','∀E, then &E.']},
  {lv:1,k:'A',name:'Relation instance',prem:['(∀x)Rxa'],goal:'(∃y)Rby',proof:[[0,'Rba','1 ∀E'],[0,'(∃y)Rby','2 ∃I']],
    hints:['Pick the instance of the universal that has the other name in front.','∀E gives `Rba`; ∃I replaces `a` with y.']},
  {lv:1,k:'A',name:'A chain of universals',prem:['(∀x)(Fx ⊃ Gx)','(∀x)(Gx ⊃ Hx)','Fa'],goal:'Ha',proof:[[0,'Fa ⊃ Ga','1 ∀E'],[0,'Ga','4, 3 ⊃E'],[0,'Ga ⊃ Ha','2 ∀E'],[0,'Ha','6, 5 ⊃E']],
    hints:['Instantiate both universals with the same name.','Then ⊃E twice.']},
  {lv:1,k:'A',name:'Two instances',prem:['(∀x)Fx'],goal:'Fa & Fb',proof:[[0,'Fa','1 ∀E'],[0,'Fb','1 ∀E'],[0,'Fa & Fb','2, 3 &I']],
    hints:['A universal can be instantiated as often as you like.','∀E twice, then &I.']},
  {lv:1,k:'A',name:'Generalizing a conjunction',prem:['Fa','Ga'],goal:'(∃x)(Fx & Gx)',proof:[[0,'Fa & Ga','1, 2 &I'],[0,'(∃x)(Fx & Gx)','3 ∃I']],
    hints:['Build the instance first.','&I, then ∃I.']},
  {lv:1,k:'T',name:'Self-implication',prem:[],goal:'(∀x)(Fx ⊃ Fx)',proof:[[1,'Fa','A / ⊃I'],[0,'Fa ⊃ Fa','1–1 ⊃I'],[0,'(∀x)(Fx ⊃ Fx)','2 ∀I']],
    hints:['Prove an instance with a fresh name, then use ∀I.','`Fa` ⊃ `Fa` comes from a one-line ⊃I subderivation.']},
  {lv:1,k:'I',name:'Substituting identicals',prem:['Fa','a = b'],goal:'Fb',proof:[[0,'Fb','2, 1 =E']],
    hints:['Identity lets you swap names.','One =E.']},
  {lv:1,k:'I',name:'Transitivity of identity',prem:['a = b','b = c'],goal:'a = c',proof:[[0,'a = c','2, 1 =E']],
    hints:['Replace `b` in the first premise using the second.','One =E.']},
  /* ---------- standard ---------- */
  {lv:2,k:'A',name:'Distributing a universal',prem:['(∀x)(Fx ⊃ Gx)','(∀x)Fx'],goal:'(∀x)Gx',proof:[[0,'Fa ⊃ Ga','1 ∀E'],[0,'Fa','2 ∀E'],[0,'Ga','3, 4 ⊃E'],[0,'(∀x)Gx','5 ∀I']],
    hints:['Derive `Ga` for a name that appears in no assumption, then ∀I.','∀E on both premises with the same fresh name.']},
  {lv:2,k:'A',name:'Existential syllogism',prem:['(∀x)(Fx ⊃ Gx)','(∃x)Fx'],goal:'(∃x)Gx',proof:[[1,'Fa','A / ∃E'],[1,'Fa ⊃ Ga','1 ∀E'],[1,'Ga','4, 3 ⊃E'],[1,'(∃x)Gx','5 ∃I'],[0,'(∃x)Gx','2, 3–6 ∃E']],
    hints:['Start ∃E: assume an instance of the existential premise with a brand-new name.','Inside, derive the goal itself; the name must not appear in it.']},
  {lv:2,k:'A',name:'Splitting a universal',prem:['(∀x)(Fx & Gx)'],goal:'(∀x)Fx',proof:[[0,'Fa & Ga','1 ∀E'],[0,'Fa','2 &E'],[0,'(∀x)Fx','3 ∀I']],
    hints:['Work with an arbitrary instance, then generalize.','∀E, &E, ∀I.']},
  {lv:2,k:'A',name:'Splitting an existential',prem:['(∃x)(Fx & Gx)'],goal:'(∃x)Fx',proof:[[1,'Fa & Ga','A / ∃E'],[1,'Fa','2 &E'],[1,'(∃x)Fx','3 ∃I'],[0,'(∃x)Fx','1, 2–4 ∃E']],
    hints:['∃E: assume an instance with a new name and derive the goal inside.','Inside: &E, then ∃I.']},
  {lv:2,k:'A',name:'Universal hypothetical syllogism',prem:['(∀x)(Fx ⊃ Gx)','(∀x)(Gx ⊃ Hx)'],goal:'(∀x)(Fx ⊃ Hx)',proof:[[0,'Fa ⊃ Ga','1 ∀E'],[0,'Ga ⊃ Ha','2 ∀E'],[1,'Fa','A / ⊃I'],[1,'Ga','3, 5 ⊃E'],[1,'Ha','4, 6 ⊃E'],[0,'Fa ⊃ Ha','5–7 ⊃I'],[0,'(∀x)(Fx ⊃ Hx)','8 ∀I']],
    hints:['Prove `Fa ⊃ Ha` for a fresh name `a`, then ∀I.','That instance is hypothetical syllogism: assume `Fa`, ⊃E twice.']},
  {lv:2,k:'A',name:'Instance by modus tollens',prem:['(∀x)(Fx ⊃ Gx)','~ Ga'],goal:'~ Fa',proof:[[0,'Fa ⊃ Ga','1 ∀E'],[1,'Fa','A / ~I'],[1,'Ga','3, 4 ⊃E'],[1,'~ Ga','2 R'],[0,'~ Fa','4–6 ~I']],
    hints:['Instantiate the universal, then argue by ~I.','Assume `Fa`: it gives `Ga`, which contradicts `~ Ga`.']},
  {lv:2,k:'A',name:'Witness with both properties',prem:['(∃x)Fx','(∀x)(Fx ⊃ Gx)'],goal:'(∃x)(Fx & Gx)',proof:[[1,'Fa','A / ∃E'],[1,'Fa ⊃ Ga','2 ∀E'],[1,'Ga','4, 3 ⊃E'],[1,'Fa & Ga','3, 5 &I'],[1,'(∃x)(Fx & Gx)','6 ∃I'],[0,'(∃x)(Fx & Gx)','1, 3–7 ∃E']],
    hints:['∃E on the first premise with a new name.','Inside, get both conjuncts and use ∃I.']},
  {lv:2,k:'T',name:'Universal implies existential',prem:[],goal:'(∀x)Fx ⊃ (∃x)Fx',proof:[[1,'(∀x)Fx','A / ⊃I'],[1,'Fa','1 ∀E'],[1,'(∃x)Fx','2 ∃I'],[0,'(∀x)Fx ⊃ (∃x)Fx','1–3 ⊃I']],
    hints:['Assume the antecedent.','∀E then ∃I. (This depends on the UD being nonempty.)']},
  {lv:2,k:'I',name:'Using an identity premise',prem:['(∀x)(Fx ⊃ x = a)','Fb'],goal:'b = a',proof:[[0,'Fb ⊃ b = a','1 ∀E'],[0,'b = a','3, 2 ⊃E']],
    hints:['Instantiate the universal with `b`.','Then ⊃E.']},
  {lv:2,k:'I',name:'Distinctness',prem:['Fa','~ Fb'],goal:'~ a = b',proof:[[1,'a = b','A / ~I'],[1,'Fb','3, 1 =E'],[1,'~ Fb','2 R'],[0,'~ a = b','3–5 ~I']],
    hints:['Assume `a = b` and look for a contradiction.','=E turns `Fa` into `Fb`.']},
  /* ---------- challenge ---------- */
  {lv:3,k:'A',name:'Swapping quantifiers',prem:['(∃x)(∀y)Rxy'],goal:'(∀y)(∃x)Rxy',proof:[[1,'(∀y)Ray','A / ∃E'],[1,'Rab','2 ∀E'],[1,'(∃x)Rxb','3 ∃I'],[1,'(∀y)(∃x)Rxy','4 ∀I'],[0,'(∀y)(∃x)Rxy','1, 2–5 ∃E']],
    hints:['∃E first: assume `(∀y)Ray` for a new name `a`.','Inside, use ∀E with another fresh name `b`, then ∃I and ∀I.']},
  {lv:3,k:'A',name:'Quantifier negation, part 1',prem:['~ (∃x)Fx'],goal:'(∀x)~ Fx',proof:[[1,'Fa','A / ~I'],[1,'(∃x)Fx','2 ∃I'],[1,'~ (∃x)Fx','1 R'],[0,'~ Fa','2–4 ~I'],[0,'(∀x)~ Fx','5 ∀I']],
    hints:['Prove `~ Fa` for a fresh name, then ∀I.','Assume `Fa`: ∃I contradicts the premise.']},
  {lv:3,k:'A',name:'Quantifier negation, part 2',prem:['(∀x)~ Fx'],goal:'~ (∃x)Fx',proof:[[1,'(∃x)Fx','A / ~I'],[2,'Fa','A / ∃E'],[3,'(∃x)Fx','A / ~I'],[3,'Fa','3 R'],[3,'~ Fa','1 ∀E'],[2,'~ (∃x)Fx','4–6 ~I'],[1,'~ (∃x)Fx','2, 3–7 ∃E'],[1,'(∃x)Fx','2 R'],[0,'~ (∃x)Fx','2–9 ~I']],
    hints:['Assume `(∃x)Fx` and aim for a contradiction (~I).','Inside, ∃E must end with a sentence without the new name: derive `~ (∃x)Fx` itself.']},
  {lv:3,k:'A',name:'Existential antecedent',prem:['(∃x)Fx ⊃ Ga'],goal:'(∀x)(Fx ⊃ Ga)',proof:[[1,'Fb','A / ⊃I'],[1,'(∃x)Fx','2 ∃I'],[1,'Ga','1, 3 ⊃E'],[0,'Fb ⊃ Ga','2–4 ⊃I'],[0,'(∀x)(Fx ⊃ Ga)','5 ∀I']],
    hints:['Prove `Fb ⊃ Ga` for a name `b` that appears nowhere else, then ∀I.','From `Fb`, ∃I gives the antecedent of the premise.']},
  {lv:3,k:'A',name:'Universal disjunctive syllogism',prem:['(∀x)(Fx ∨ Gx)','(∀x)~ Fx'],goal:'(∀x)Gx',proof:[[0,'Fa ∨ Ga','1 ∀E'],[0,'~ Fa','2 ∀E'],[1,'Fa','A / ∨E'],[2,'~ Ga','A / ~E'],[2,'Fa','5 R'],[2,'~ Fa','4 R'],[1,'Ga','6–8 ~E'],[1,'Ga','A / ∨E'],[0,'Ga','3, 5–9, 10–10 ∨E'],[0,'(∀x)Gx','11 ∀I']],
    hints:['Instantiate both premises with a fresh name, then ∨E.','In the `Fa` case, `Ga` follows by ~E from the contradiction with `~ Fa`.']},
  {lv:3,k:'A',name:'Existential over a conjunction',prem:['(∃x)(Fx & Gx)'],goal:'(∃x)Fx & (∃x)Gx',proof:[[1,'Fa & Ga','A / ∃E'],[1,'Fa','2 &E'],[1,'Ga','2 &E'],[1,'(∃x)Fx','3 ∃I'],[1,'(∃x)Gx','4 ∃I'],[1,'(∃x)Fx & (∃x)Gx','5, 6 &I'],[0,'(∃x)Fx & (∃x)Gx','1, 2–7 ∃E']],
    hints:['∃E, and derive the whole goal inside.','Split the instance, generalize each half, join them.']},
  {lv:3,k:'A',name:'Universals over a conjunction',prem:['(∀x)Fx & (∀x)Gx'],goal:'(∀x)(Fx & Gx)',proof:[[0,'(∀x)Fx','1 &E'],[0,'(∀x)Gx','1 &E'],[0,'Fa','2 ∀E'],[0,'Ga','3 ∀E'],[0,'Fa & Ga','4, 5 &I'],[0,'(∀x)(Fx & Gx)','6 ∀I']],
    hints:['Split the premise, instantiate both with the same fresh name.','&I, then ∀I.']},
  {lv:3,k:'T',name:'Symmetry of identity',prem:[],goal:'(∀x)(∀y)(x = y ⊃ y = x)',proof:[[1,'a = b','A / ⊃I'],[1,'(∀x)x = x','=I'],[1,'a = a','2 ∀E'],[1,'b = a','1, 3 =E'],[0,'a = b ⊃ b = a','1–4 ⊃I'],[0,'(∀y)(a = y ⊃ y = a)','5 ∀I'],[0,'(∀x)(∀y)(x = y ⊃ y = x)','6 ∀I']],
    pde:true,hints:['Prove `a = b ⊃ b = a` for fresh names, then ∀I twice.','=I gives `(∀x)x = x`; replace one `a` in `a = a` using `a = b`.']},
  {lv:3,k:'T',name:'A theorem about relations',prem:[],goal:'(∃x)(∀y)Rxy ⊃ (∀y)(∃x)Rxy',proof:[[1,'(∃x)(∀y)Rxy','A / ⊃I'],[2,'(∀y)Ray','A / ∃E'],[2,'Rab','2 ∀E'],[2,'(∃x)Rxb','3 ∃I'],[2,'(∀y)(∃x)Rxy','4 ∀I'],[1,'(∀y)(∃x)Rxy','1, 2–5 ∃E'],[0,'(∃x)(∀y)Rxy ⊃ (∀y)(∃x)Rxy','1–6 ⊃I']],
    hints:['Assume the antecedent; inside, it\'s the quantifier swap.','∃E, ∀E, ∃I, ∀I, then discharge.']},
  {lv:3,k:'I',name:'Exactly one, used',prem:['(∃x)(Fx & (∀y)(Fy ⊃ y = x))','Fa','Fb'],goal:'a = b',proof:[[1,'Fc & (∀y)(Fy ⊃ y = c)','A / ∃E'],[1,'(∀y)(Fy ⊃ y = c)','4 &E'],[1,'Fa ⊃ a = c','5 ∀E'],[1,'a = c','6, 2 ⊃E'],[1,'Fb ⊃ b = c','5 ∀E'],[1,'b = c','8, 3 ⊃E'],[1,'a = b','9, 7 =E'],[0,'a = b','1, 4–10 ∃E']],
    hints:['∃E on the first premise with a new name `c`.','Show `a = c` and `b = c`, then =E gives `a = b`.']}
];
/* mark which rules each model proof uses, and which system it needs */
T.forEach(t=>{t.rules=[...new Set(t.proof.map(p=>(p[2].match(/(∀E|∀I|∃E|∃I|⊃I|~I|~E|∨E|=E|=I)$/)||[])[1]).filter(Boolean))];if(t.k==='I'||t.proof.some(p=>/=[EI]$/.test(p[2])))t.pde=true});

/* rename predicate letters and constants character by character */
const PRED=['F','G','H','R'],CONS=['a','b','c'];
function rename(s,m){let o='';for(const ch of s)o+=m[ch]??ch;return o}

function generate(opts){
  const seed=opts.seed>>>0,level=opts.level||1,kind=opts.kind||'A';
  const want=(opts.rules||[]).filter(r=>RULES.includes(r));
  const r=rng(seed),pick=a=>a[Math.floor(r()*a.length)];
  let pool=T.filter(t=>t.k===kind&&t.lv===level);
  if(!pool.length)pool=T.filter(t=>t.k===kind);
  if(want.length){const hit=pool.filter(t=>want.some(w=>t.rules.includes(w)));if(hit.length)pool=hit;else{const any=T.filter(t=>t.k===kind&&want.some(w=>t.rules.includes(w)));if(any.length)pool=any}}
  for(let attempt=0;attempt<40;attempt++){
    const t=pick(pool);
    const preds='BCDFGHJKLMNPQSTW'.split('').sort(()=>r()-0.5),cons='abcdefghijkmnpqrst'.split('').sort(()=>r()-0.5);
    const m={};PRED.forEach((p,i)=>m[p]=preds[i]);CONS.forEach((c,i)=>m[c]=cons[i]);
    const prem=t.prem.map(s=>rename(s,m)),goal=rename(t.goal,m);
    const lines=[...prem.map(p=>[0,p,'Assumption']),...t.proof.map(([d,s,j])=>[d,rename(s,m),j])];
    const text='Derive: '+goal+'\n'+lines.map(([d,s,j])=>'| '.repeat(d+1)+s+'    '+j).join('\n')+'\n';
    const sys=t.pde?'PDE':'PD';
    const chk=SDX.check(text,sys,PL);
    if(!chk.summary||!chk.summary.ok)continue;
    return{pattern:t.name,kind:t.k,level,system:sys,goal:parse(goal).ast,premises:prem.map(s=>parse(s).ast),solution:text,rules:t.rules,
      hintList:t.hints.map(h=>renameHint(h,m)),
      start:'Derive: '+goal+'\n'+prem.map(p=>'| '+p+'    Assumption').join('\n')+(prem.length?'\n':'')};
  }
  return null;
}
/* hints mark formulas and names with backticks; only those are renamed */
function renameHint(h,m){return h.replace(/`([^`]+)`/g,(x,f)=>rename(f,m))}
/* problem codes: D, level, kind, rule mask, seed — e.g. D2A-0-k3j9a */
function encode(o){const mask=RULES.reduce((s,r,i)=>s|((o.rules||[]).includes(r)?1<<i:0),0);return 'D'+o.level+(o.kind||'A')+'-'+mask.toString(36)+'-'+(o.seed>>>0).toString(36)}
function decode(s){const x=String(s).trim().match(/^D([123])([ATI])-([0-9a-z]+)-([0-9a-z]+)$/i);if(!x)return null;
  const mask=parseInt(x[3],36);return{level:+x[1],kind:x[2].toUpperCase(),rules:RULES.filter((r,i)=>mask&(1<<i)),seed:parseInt(x[4],36)>>>0}}
window.PDGEN={generate,encode,decode,RULES,LEVELS,PATTERNS:T};
})();
