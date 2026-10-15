/* Valid Moves: a click-to-build editor for derivations.
   The student types only the sentence; the rule is a button, cited lines are picked by
   clicking line numbers, and scope lines are handled automatically. The derivation is
   still stored as the plain-text format that derive.js checks, so the text editor
   remains available as an alternative. Requires logic.js and derive.js (and pl.js for PL). */
(function(){
const esc=SL.esc;
const RANGE_RULES=['⊃I','~I','~E','∨E','≡I'];
const ASSUME_FOR=['⊃I','~I','~E','∨E','≡I'];
const HINT={
  'Assumption':'A premise. Premises go at the top of the derivation.',
  'assume':'Starts a new subderivation, one scope line further in.',
  'R':'Click the line to repeat.',
  '&I':'Click the two lines you are joining.',
  '&E':'Click the conjunction.',
  '∨I':'Click the line you are adding a disjunct to.',
  '∨E':'Click the disjunction, then the assumption line of each of the two subderivations.',
  '⊃I':'Click the assumption line of the subderivation that goes from P to Q.',
  '⊃E':'Click the conditional and its antecedent.',
  '~I':'Click the assumption line of the subderivation that reached Q and ~ Q.',
  '~E':'Click the assumption line of the subderivation that reached Q and ~ Q.',
  '≡I':'Click the assumption lines of the two subderivations.',
  '≡E':'Click the biconditional and the side you have.',
  'MT':'Click the conditional and the negation of its consequent.',
  'HS':'Click the two conditionals.',
  'DS':'Click the disjunction and the negation of one disjunct.',
  'repl':'Click the line you are rewriting. One replacement per line.',
  '∀E':'Click the universally quantified sentence.',
  '∃I':'Click the substitution instance.',
  '∀I':'Click the substitution instance. Its constant must not appear in an open assumption or in the result.',
  '∃E':'Click the existential sentence, then the assumption line of the subderivation.',
  'QN':'Click the line you are rewriting.',
  '=I':'Cites nothing. Type a sentence like (∀x)x = x.',
  '=E':'Click the identity sentence and the sentence you are rewriting.'
};
const REPL=['Com','Assoc','Impl','DN','DeM','Idem','Trans','Exp','Dist','Equiv','QN'];

/* cfg: {root, out, lang, groups:[{label, rules:[...], when:()=>bool}], getText, setText, getResult, assumeFor} */
function mount(cfg){
  const L=cfg.lang||SL;
  const R=cfg.root;
  let rule=null,assumeFor=null,cites=[],ends=0,err='';
  R.innerHTML=
    '<div class="db">'+
      '<div class="db-scope" id="db-scope"></div>'+
      '<label class="db-lbl" for="db-sent">1 · Sentence for the next line</label>'+
      '<div class="entry"><input id="db-sent" type="text" spellcheck="false" autocomplete="off" aria-label="Sentence for the next line"></div>'+
      '<div id="db-keys"></div>'+
      '<div class="db-lbl">2 · Rule</div>'+
      '<div id="db-rules" class="db-rules"></div>'+
      '<div class="db-lbl">3 · Lines it cites</div>'+
      '<div class="db-cites" id="db-cites"></div>'+
      '<p class="note" id="db-hint"></p>'+
      '<div class="cta"><button type="button" class="btn" id="db-add">Add line</button><button type="button" class="btn ghost" id="db-undo">Remove last line</button><button type="button" class="btn ghost" id="db-reset">Start over</button></div>'+
      '<p class="err" id="db-err" aria-live="polite"></p>'+
    '</div>';
  const $=id=>R.querySelector('#'+id);
  const sent=$('db-sent');
  $('db-keys').innerHTML=L.KEYS_HTML;
  L.wireInput(sent,$('db-keys'),()=>{err='';paint()});

  const lines=()=>(cfg.getResult()||{lines:[]}).lines;
  const allPrimary=()=>lines().every(l=>l.d===0&&l.just&&l.just.assume);
  const curDepth=()=>{const ls=lines();if(!ls.length)return 0;return Math.max(0,ls[ls.length-1].d-ends)};
  const subOf=n=>((cfg.getResult()||{}).subs||[]).find(s=>s.start===n);
  function depthForNew(){
    if(rule==='Assumption')return 0;
    if(rule==='assume')return curDepth()+1;
    if(RANGE_RULES.includes(rule)||rule==='∃E'){
      const ranges=cites.filter(c=>c.b!==undefined);
      if(ranges.length){const ds=ranges.map(c=>{const ln=lines()[c.a-1];return ln?ln.d:1});return Math.max(0,Math.min(...ds)-1)}
    }
    return curDepth();
  }
  function citeText(){return cites.map(c=>c.b!==undefined?c.a+'–'+c.b:String(c.a)).join(', ')}
  function paint(){
    const groups=cfg.groups.filter(g=>!g.when||g.when());
    let h='';
    h+='<div class="db-group"><span class="db-glbl">Assume</span>'+
      '<button type="button" class="key rb" data-r="Assumption" aria-pressed="'+(rule==='Assumption')+'"'+(allPrimary()?'':' disabled title="Premises go at the top"')+'>Premise</button>'+
      (cfg.assumeFor||ASSUME_FOR).map(f=>'<button type="button" class="key rb" data-r="assume" data-f="'+f+'" aria-pressed="'+(rule==='assume'&&assumeFor===f)+'" title="Start a subderivation to be discharged by '+f+'">A / '+esc(f)+'</button>').join('')+'</div>';
    groups.forEach(g=>{h+='<div class="db-group"><span class="db-glbl">'+esc(g.label)+'</span>'+g.rules.map(r=>'<button type="button" class="key rb" data-r="'+esc(r)+'" aria-pressed="'+(rule===r)+'">'+esc(r)+'</button>').join('')+'</div>'});
    $('db-rules').innerHTML=h;
    const needsCites=rule&&rule!=='Assumption'&&rule!=='assume'&&rule!=='=I';
    $('db-cites').innerHTML=needsCites?(cites.length?cites.map((c,i)=>'<span class="chip">'+(c.b!==undefined?c.a+'–'+c.b:c.a)+' <button type="button" class="chip-x" data-i="'+i+'" aria-label="Remove">×</button></span>').join(''):'<span class="note">Click line numbers in the derivation.</span>'):'<span class="note">'+(rule?'None needed.':'Choose a rule first.')+'</span>';
    const key=rule==='assume'?'assume':REPL.includes(rule)&&rule!=='QN'?'repl':rule;
    $('db-hint').textContent=rule?(HINT[key]||'')+(rule==='assume'&&curDepth()>0&&(assumeFor==='∨E'||assumeFor==='≡I')?' If this is the second subderivation, click End subderivation first so it sits beside the first one.':''):'';
    cfg.out.classList.toggle('pick',!!needsCites);
    const d=depthForNew(),cd=curDepth();
    $('db-scope').innerHTML='<span class="note">Next line goes '+(d===0?'on the <b>main scope line</b>':'inside <b>'+d+'</b> subderivation'+(d>1?'s':''))+'.</span>'+
      (cd>0?' <button type="button" class="key" id="db-end" title="The next line goes one scope line further out">End subderivation</button>':'')+
      (ends>0?' <button type="button" class="key" id="db-unend">Undo end</button>':'');
    $('db-err').textContent=err;
  }
  R.addEventListener('click',e=>{
    const b=e.target.closest('button');if(!b)return;
    if(b.classList.contains('rb')){
      const r=b.dataset.r;
      if(rule===r&&(r!=='assume'||assumeFor===b.dataset.f)){rule=null;assumeFor=null}else{rule=r;assumeFor=b.dataset.f||null}
      cites=[];err='';paint();return;
    }
    if(b.classList.contains('chip-x')){cites.splice(+b.dataset.i,1);paint();return}
    if(b.id==='db-end'){ends++;paint();return}
    if(b.id==='db-unend'){ends=Math.max(0,ends-1);paint();return}
    if(b.id==='db-add')return add();
    if(b.id==='db-undo'){const t=cfg.getText().replace(/\s+$/,'').split('\n');for(let i=t.length-1;i>=0;i--){if(t[i].trim()&&!/^\s*Derive\s*:/i.test(t[i])){t.splice(i,1);break}}cfg.setText(t.join('\n')+'\n');ends=0;err='';paint();return}
    if(b.id==='db-reset'){cfg.reset();rule=null;cites=[];ends=0;err='';sent.value='';paint();return}
  });
  /* picking cited lines from the rendered derivation */
  cfg.out.addEventListener('click',e=>{
    const fn=e.target.closest('.fn');if(!fn||!cfg.out.classList.contains('pick'))return;
    const n=+fn.textContent;if(!n)return;
    const ln=lines()[n-1];
    let c={a:n};
    if((RANGE_RULES.includes(rule)||rule==='∃E')&&ln&&ln.just&&ln.just.assume&&ln.d>0){const s=subOf(n);if(s)c={a:s.start,b:s.last}}
    if(!cites.some(x=>x.a===c.a&&x.b===c.b))cites.push(c);
    paint();
  });
  function add(){
    err='';
    if(!sent.value.trim()){err='Type the sentence for this line first.';return paint()}
    try{L.parse(sent.value)}catch(e){err='The sentence isn\'t right yet: '+e.message;return paint()}
    if(!rule){err='Choose the rule that justifies this line.';return paint()}
    const d=depthForNew();
    let just=rule==='Assumption'?'Assumption':rule==='assume'?'A / '+assumeFor:rule==='=I'?'=I':(citeText()+' '+rule).trim();
    if(rule!=='Assumption'&&rule!=='assume'&&rule!=='=I'&&!cites.length){err='Click the line or lines this rule uses.';return paint()}
    const line='| '.repeat(d+1)+L.normalize(sent.value.trim()).replace(/Equi∨/g,'Equiv')+'    '+just;
    let t=cfg.getText();if(t&&!t.endsWith('\n'))t+='\n';
    cfg.setText(t+line+'\n');
    sent.value='';rule=null;assumeFor=null;cites=[];ends=0;
    paint();
    sent.focus();
  }
  paint();
  return{refresh:paint,clear:()=>{rule=null;cites=[];ends=0;err='';paint()}};
}
window.DB={mount};
})();
