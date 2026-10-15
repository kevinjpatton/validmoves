/* Valid Moves: truth-trees for PL (The Logic Book, ch. 9).
   Adds ~∀D, ~∃D, ∃D (foreign constant), ∃D2 (Boolos's branching rule) and ∀D
   (never checked off) to the SL rules, and uses the book's definition of a completed
   open branch for PL. Renders with TT.render. Requires logic.js, pl.js, trees.js. */
(function(){
const {key,show,showTop,subst,constants,eq}=PL;
const N=a=>({op:'~',a});
const isLit=a=>a.op==='atom'||(a.op==='~'&&a.a.op==='atom');
const litKey=a=>a.op==='atom'?key(a):'~'+key(a.a);
const LET='abcdefghijklmnopqrstuv'.split('');
/* a, b, …, v, then a1, b1, …: never runs out */
function fresh(used){for(let k=0;;k++){for(const c of LET){const n=k?c+k:c;if(!used.has(n))return n}}}
function sentRule(a){
  if(a.op==='~'){const b=a.a;
    if(b.op==='~')return{name:'~~D',br:[[b.a]]};
    if(b.op==='∨')return{name:'~∨D',br:[[N(b.l),N(b.r)]]};
    if(b.op==='⊃')return{name:'~⊃D',br:[[b.l,N(b.r)]]};
    if(b.op==='&')return{name:'~&D',br:[[N(b.l)],[N(b.r)]]};
    if(b.op==='≡')return{name:'~≡D',br:[[b.l,N(b.r)],[N(b.l),b.r]]};
    if(b.op==='∀')return{name:'~∀D',br:[[{op:'∃',v:b.v,a:N(b.a)}]]};
    if(b.op==='∃')return{name:'~∃D',br:[[{op:'∀',v:b.v,a:N(b.a)}]]};
    return null;
  }
  if(a.op==='&')return{name:'&D',br:[[a.l,a.r]]};
  if(a.op==='∨')return{name:'∨D',br:[[a.l],[a.r]]};
  if(a.op==='⊃')return{name:'⊃D',br:[[N(a.l)],[a.r]]};
  if(a.op==='≡')return{name:'≡D',br:[[a.l,a.r],[N(a.l),N(a.r)]]};
  return null;
}
function clashes(L){for(const k of L){if(k[0]!=='~'&&L.has('~'+k))return true}return false}
const inst=(q,c)=>subst(q.a,q.v,{t:'con',n:c});

class PTree{
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
  closed(leaf){const L=this.lits(leaf);if(clashes(L))return true;
    /* PLE: a branch with ~ a = a is closed */
    return this.pathOf(leaf).some(e=>e.a.op==='~'&&e.a.a.op==='atom'&&e.a.a.pred==='='&&key({op:'atom',pred:'x',args:[e.a.a.args[0]]})===key({op:'atom',pred:'x',args:[e.a.a.args[1]]}))}
  consts(leaf){const S=new Set();this.pathOf(leaf).forEach(e=>constants(e.a,S));return S}
  allEntries(n=this.root){return [...n.entries,...n.children.flatMap(c=>this.allEntries(c))]}
  openUnder(e){return this.leaves(e.node).filter(l=>!this.closed(l))}
  /* universal: which constants still need an instance on a given leaf */
  missing(e,leaf){
    const keys=new Set(this.pathOf(leaf).map(x=>key(x.a)));
    const cs=[...this.consts(leaf)];
    const need=cs.filter(c=>!keys.has(key(inst(e.a,c))));
    const any=cs.some(c=>keys.has(key(inst(e.a,c))));
    if(!cs.length)return['a'];
    return need.length?need:(any?[]:[cs[0]]);
  }
  completedOpen(leaf){
    if(this.closed(leaf))return false;
    return this.pathOf(leaf).every(e=>isLit(e.a)||(e.a.op==='∀'?this.missing(e,leaf).length===0&&this.hasInstance(e,leaf):e.checked));
  }
  hasInstance(e,leaf){const keys=new Set(this.pathOf(leaf).map(x=>key(x.a)));return[...this.consts(leaf)].some(c=>keys.has(key(inst(e.a,c))))}
  candidates(){
    return this.allEntries().filter(e=>{
      if(isLit(e.a))return false;
      const open=this.openUnder(e);if(!open.length)return false;
      if(e.a.op==='∀')return open.some(l=>this.missing(e,l).length);
      return !e.checked;
    }).sort((x,y)=>x.line-y.line);
  }
  freshFor(leaves){const used=new Set();leaves.forEach(l=>this.consts(l).forEach(c=>used.add(c)));return fresh(used)}
  /* mode for ∃: 'D' (foreign constant) or 'D2' (branching); c for ∀ */
  decompose(e,opt={}){
    const targets=this.openUnder(e),start=this.line+1;let n=1,name;
    if(e.a.op==='∀'){
      const c=opt.c||this.missing(e,targets.find(l=>this.missing(e,l).length)||targets[0])[0];
      const s=inst(e.a,c);
      targets.forEach(leaf=>{const keys=new Set(this.pathOf(leaf).map(x=>key(x.a)));if(!keys.has(key(s)))leaf.entries.push(this.entry(s,start,leaf))});
      name='∀D';this.steps.push({id:e.id,c});
    }else if(e.a.op==='∃'){
      if(opt.mode==='D2'){
        targets.forEach(leaf=>{
          const cs=[...this.consts(leaf)].sort();
          const all=[...cs,fresh(new Set(cs))];
          if(all.length===1)leaf.entries.push(this.entry(inst(e.a,all[0]),start,leaf));
          else leaf.children=all.map(c=>{const ch={entries:[],children:[],parent:leaf};ch.entries.push(this.entry(inst(e.a,c),start,ch));return ch});
        });
        name='∃D2';
      }else{
        const c=this.freshFor(targets);
        targets.forEach(leaf=>leaf.entries.push(this.entry(inst(e.a,c),start,leaf)));
        name='∃D';
      }
      e.checked=true;this.steps.push({id:e.id,mode:opt.mode||'D'});
    }else{
      const r=sentRule(e.a);n=Math.max(...r.br.map(b=>b.length));name=r.name;
      targets.forEach(leaf=>{
        if(r.br.length===1)r.br[0].forEach((s,i)=>leaf.entries.push(this.entry(s,start+i,leaf)));
        else leaf.children=r.br.map(list=>{const c={entries:[],children:[],parent:leaf};list.forEach((s,i)=>c.entries.push(this.entry(s,start+i,c)));return c});
      });
      e.checked=true;this.steps.push({id:e.id});
    }
    for(let k=0;k<n;k++)this.just[start+k]=e.line+' '+name;
    this.line+=n;
  }
  wouldClose(e){
    const r=sentRule(e.a);if(!r)return false;
    return this.openUnder(e).some(l=>{const L=this.lits(l);return r.br.some(list=>{const S=new Set(L);list.filter(isLit).forEach(a=>S.add(litKey(a)));return clashes(S)})});
  }
  /* A systematic order: non-branching, closing, universal instances, existentials, other branching. */
  /* Work on one branch at a time: the open branch with the fewest constants, then the
     leftmost. Only sentences on that branch that still need work there are considered. */
  focus(){
    const open=this.leaves().filter(l=>!this.closed(l)&&!this.completedOpen(l));
    if(!open.length)return null;
    return open.map((l,i)=>({l,i,k:this.consts(l).size})).sort((x,y)=>x.k-y.k||x.i-y.i)[0].l;
  }
  suggest(mode){
    const f=this.focus();if(!f)return null;
    const onF=new Set(this.pathOf(f));
    const c=this.candidates().filter(e=>onF.has(e)&&(e.a.op!=='∀'||this.missing(e,f).length));
    if(!c.length)return null;
    const tf=c.filter(e=>e.a.op!=='∀'&&e.a.op!=='∃');
    const nb=tf.find(e=>sentRule(e.a).br.length===1);if(nb)return{e:nb,why:'it doesn\'t branch'};
    const cl=tf.find(e=>this.wouldClose(e));if(cl)return{e:cl,why:'it closes a branch'};
    const ex=c.find(e=>e.a.op==='∃');if(ex)return{e:ex,why:'an existential is ready to decompose with '+(mode==='D2'?'∃D2':'∃D')};
    const u=c.find(e=>e.a.op==='∀');if(u)return{e:u,c:this.missing(u,f)[0],why:'a universal still needs an instance for a constant on the branch'};
    const weight=e=>sentRule(e.a).br.flat().reduce((s,a)=>s+show(a).length,0);
    return{e:[...tf].sort((x,y)=>weight(y)-weight(x)||x.line-y.line)[0],why:'it is the most complex sentence left'};
  }
  answerKnown(){const L=this.leaves();return L.every(l=>this.closed(l))||L.some(l=>this.completedOpen(l))}
  isClosed(){return this.leaves().every(l=>this.closed(l))}
  done(){return !this.candidates().length}
  auto(stopEarly,mode,maxLines=60){
    let g=0;
    while(!this.done()&&!(stopEarly&&this.answerKnown())&&this.line<maxLines&&g++<400){const s=this.suggest(mode);if(!s)break;this.decompose(s.e,{mode,c:s.c})}
    this.hitLimit=!this.done()&&!(stopEarly&&this.answerKnown())&&this.line>=maxLines;
    return this;
  }
  findById(id){return this.allEntries().find(e=>e.id===id)}
  /* A model read off a completed open branch: one member per constant. */
  model(leaf){
    const cs=[...this.consts(leaf)].sort(),idx=Object.fromEntries(cs.map((c,i)=>[c,i]));
    const nm=i=>String(i+1);
    const lines=['UD: {'+cs.map((c,i)=>nm(i)).join(', ')+'}'];
    cs.forEach(c=>lines.push(c+': '+nm(idx[c])));
    const preds={},letters={};
    this.pathOf(leaf).forEach(e=>{if(e.a.op==='atom'&&e.a.pred!=='='){if(!e.a.args.length)letters[e.a.pred]=true;else(preds[e.a.pred]=preds[e.a.pred]||[]).push(e.a.args.map(t=>nm(idx[t.n])).join(','))}});
    const V={preds:{},consts:new Set(),fns:{},letters:new Set()};this.asts.forEach(a=>PL.vocab(a,V));
    [...V.letters].sort().forEach(l=>lines.push(l+': '+(letters[l]?'T':'F')));
    Object.entries(V.preds).sort().forEach(([p,k])=>lines.push(p+': {'+[...new Set(preds[p]||[])].map(x=>k>1?'<'+x+'>':x).join(', ')+'}'));
    return lines;
  }
}
function replay(asts,steps){const t=new PTree(asts);for(const s of steps){const e=t.findById(s.id);if(!e)break;t.decompose(e,s)}return t}
window.PTT={PTree,replay,sentRule,isLit};
})();
