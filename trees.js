/* Valid Moves: truth-trees for SL, following The Logic Book ch. 4.
   Each decomposition enters its results on every open branch through the sentence,
   uses one rule and one source line per tree line, and checks the sentence off.
   Requires logic.js (window.SL). */
(function(){
const {show,showTop,esc}=SL;
const neg=a=>({op:'~',a});
const isLit=a=>!!(a.v||(a.op==='~'&&a.a.v));
function rule(a){
  if(a.op==='~'){const b=a.a;
    if(b.op==='~')return{name:'~~D',full:'Negated Negation Decomposition',br:[[b.a]]};
    if(b.op==='∨')return{name:'~∨D',full:'Negated Disjunction Decomposition',br:[[neg(b.l),neg(b.r)]]};
    if(b.op==='⊃')return{name:'~⊃D',full:'Negated Material Conditional Decomposition',br:[[b.l,neg(b.r)]]};
    if(b.op==='&')return{name:'~&D',full:'Negated Conjunction Decomposition',br:[[neg(b.l)],[neg(b.r)]]};
    if(b.op==='≡')return{name:'~≡D',full:'Negated Biconditional Decomposition',br:[[b.l,neg(b.r)],[neg(b.l),b.r]]};
    return null;
  }
  if(a.op==='&')return{name:'&D',full:'Conjunction Decomposition',br:[[a.l,a.r]]};
  if(a.op==='∨')return{name:'∨D',full:'Disjunction Decomposition',br:[[a.l],[a.r]]};
  if(a.op==='⊃')return{name:'⊃D',full:'Conditional Decomposition',br:[[neg(a.l)],[a.r]]};
  if(a.op==='≡')return{name:'≡D',full:'Biconditional Decomposition',br:[[a.l,a.r],[neg(a.l),neg(a.r)]]};
  return null;
}
const litKey=a=>a.v?a.v:'~'+a.a.v;
function clashes(lits){for(const k of lits){if(k[0]!=='~'&&lits.has('~'+k))return true}return false}

class Tree{
  constructor(asts){
    this.asts=asts;this.line=0;this.nid=0;this.just={};this.steps=[];
    this.root={entries:[],children:[]};
    asts.forEach(a=>this.root.entries.push(this.entry(a,++this.line,this.root)));
    asts.forEach((a,i)=>this.just[i+1]='SM');
  }
  entry(a,line,node){return{id:++this.nid,a,line,node,checked:false}}
  leaves(n=this.root){return n.children.length?n.children.flatMap(c=>this.leaves(c)):[n]}
  pathOf(leaf){const out=[];let n=leaf;while(n){out.unshift(...n.entries);n=n.parent}return out}
  lits(leaf){return new Set(this.pathOf(leaf).filter(e=>isLit(e.a)).map(e=>litKey(e.a)))}
  closed(leaf){return clashes(this.lits(leaf))}
  open(){return this.leaves().filter(l=>!this.closed(l))}
  completedOpen(leaf){return !this.closed(leaf)&&this.pathOf(leaf).every(e=>isLit(e.a)||e.checked)}
  allEntries(n=this.root){return [...n.entries,...n.children.flatMap(c=>this.allEntries(c))]}
  candidates(){
    return this.allEntries().filter(e=>!e.checked&&!isLit(e.a)&&this.leaves(e.node).some(l=>!this.closed(l)))
      .sort((x,y)=>x.line-y.line);
  }
  decompose(e){
    const r=rule(e.a),targets=this.leaves(e.node).filter(l=>!this.closed(l));
    const n=Math.max(...r.br.map(b=>b.length)),start=this.line+1;
    targets.forEach(leaf=>{
      if(r.br.length===1) r.br[0].forEach((s,i)=>leaf.entries.push(this.entry(s,start+i,leaf)));
      else leaf.children=r.br.map(list=>{const c={entries:[],children:[],parent:leaf};list.forEach((s,i)=>c.entries.push(this.entry(s,start+i,c)));return c});
    });
    for(let k=0;k<n;k++)this.just[start+k]=e.line+' '+r.name;
    this.line+=n;e.checked=true;this.steps.push(e.id);
  }
  wouldClose(e){
    const r=rule(e.a);
    return this.leaves(e.node).filter(l=>!this.closed(l)).some(l=>{const L=this.lits(l);
      return r.br.some(list=>{const S=new Set(L);list.filter(isLit).forEach(a=>S.add(litKey(a)));return clashes(S)})});
  }
  /* The book's guidelines: non-branching first, then branching that closes a branch, then the most complex. */
  suggest(){
    const c=this.candidates();if(!c.length)return null;
    const nb=c.find(e=>rule(e.a).br.length===1);if(nb)return{e:nb,why:'it doesn\'t branch (guideline 2)'};
    const cl=c.find(e=>this.wouldClose(e));if(cl)return{e:cl,why:'decomposing it closes a branch (guideline 3)'};
    const weight=e=>rule(e.a).br.flat().reduce((s,a)=>s+show(a).length,0);
    const big=[...c].sort((x,y)=>weight(y)-weight(x)||x.line-y.line)[0];
    return{e:big,why:'it is the most complex sentence left (guideline 4)'};
  }
  answerKnown(){const L=this.leaves();return L.every(l=>this.closed(l))||L.some(l=>this.completedOpen(l))}
  isClosed(){return this.leaves().every(l=>this.closed(l))}
  done(){return !this.candidates().length}
  auto(stopEarly){let g=0;while(!this.done()&&!(stopEarly&&this.answerKnown())&&g++<200){this.decompose(this.suggest().e)}return this}
  findById(id){return this.allEntries().find(e=>e.id===id)}
  /* Assignments recovered from each completed open branch. */
  assignments(){
    const letters=SL.sortLetters([...this.asts.reduce((s,a)=>SL.letters(a,s),new Set())]);
    return this.leaves().filter(l=>this.completedOpen(l)).map(l=>{const L=this.lits(l);
      return letters.map(v=>v+' = '+(L.has(v)?'T':L.has('~'+v)?'F':'T or F')).join(', ')});
  }
}
function replay(asts,steps){const t=new Tree(asts);for(const s of steps){const e=t.findById(s);if(!e||e.checked||isLit(e.a))break;t.decompose(e)}return t}

/* Render as a grid: one row per line (plus connector rows), one column per final branch. */
function render(t,opts={}){
  const leaves=t.leaves(),N=leaves.length,range=new Map();
  (function span(n){if(!n.children.length){const i=leaves.indexOf(n);range.set(n,[i,i]);return[i,i]}
    const r=n.children.map(span);const a=[r[0][0],r[r.length-1][1]];range.set(n,a);return a})(t.root);
  const sTop=opts.showTop||showTop,sFull=opts.show||show;
  const longest=Math.max(...t.allEntries().map(e=>sFull(e.a).length));
  const colw=Math.min(Math.max(longest+3,9),30);
  const cand=new Set(opts.clickable?t.candidates().map(e=>e.id):[]);
  let h='<div class="tree" style="grid-template-columns:3.5ch repeat('+N+',minmax('+colw+'ch,1fr)) minmax(7ch,auto)">';
  for(let L=1;L<=t.line;L++){
    h+='<div class="tl" style="grid-row:'+(2*L)+'">'+L+'</div><div class="tj" style="grid-row:'+(2*L)+';grid-column:'+(N+2)+'">'+esc(t.just[L]||'')+'</div>';
  }
  (function walk(n){
    const [a,b]=range.get(n);
    n.entries.forEach(e=>{
      const txt=esc(sTop(e.a))+(e.checked?' <span class="ck">✓</span>':'');
      const inner=cand.has(e.id)?'<button type="button" class="te-btn'+(opts.hint===e.id?' hint':'')+'" data-id="'+e.id+'" title="Decompose line '+e.line+'">'+txt+'</button>':txt;
      h+='<div class="te" style="grid-row:'+(2*e.line)+';grid-column:'+(a+2)+'/'+(b+3)+'">'+inner+'</div>';
    });
    if(n.children.length){
      const k=n.children[0].entries[0].line,w=b-a+1;
      const xs=n.children.map(c=>{const[ca,cb]=range.get(c);return((ca+cb+1)/2-a)/w*100});
      h+='<div class="tc" style="grid-row:'+(2*k-1)+';grid-column:'+(a+2)+'/'+(b+3)+'"><svg viewBox="0 0 100 10" preserveAspectRatio="none" aria-hidden="true">'+xs.map(x=>'<line x1="50" y1="0" x2="'+x+'" y2="10" vector-effect="non-scaling-stroke"/>').join('')+'</svg></div>';
      n.children.forEach(walk);
    }else{
      const last=Math.max(...t.pathOf(n).map(e=>e.line));
      const mark=t.closed(n)?'<span class="tx" title="Closed branch">×</span>':t.completedOpen(n)?'<span class="to" title="Completed open branch">o</span>':'';
      if(mark)h+='<div class="tm" style="grid-row:'+(2*last+1)+';grid-column:'+(a+2)+'/'+(b+3)+'">'+mark+'</div>';
    }
  })(t.root);
  return h+'</div>';
}
window.TT={Tree,rule,isLit,replay,render,neg};
})();
