/* Valid Moves: chapter video overviews (made with NotebookLM, hosted on YouTube).
   To add a video, put its YouTube ID next to the chapter number in VIDEOS.
   The ID is the part after youtu.be/ or after watch?v= in the link. */
(function(){
const VIDEOS={
  1:'pGBNoRk-AmU'
};
/* what to listen for while watching, per chapter */
const WATCH_FOR={
  1:['How validity differs from soundness, and why a valid argument can have a false conclusion.','What makes a sentence logically true, false or indeterminate.','The special cases: why inconsistent premises make any argument valid.'],
  2:['What counts as a sentence of SL, and why every binary connective needs brackets.','How to tell the main connective of a long sentence.','"If" versus "only if", and when a connective is not truth-functional.'],
  3:['What a truth-value assignment is, and how a truth-table covers them all.','The difference between a full and a shortened truth-table.','How every property can be restated as consistency (3.6).'],
  4:['Which decomposition rules branch and which don\'t.','When a branch is closed, and when it is a completed open branch.','How to choose which set to build a tree for.'],
  5:['The difference between primary and auxiliary assumptions.','What makes a line or subderivation accessible.','How to work backwards from the goal.'],
  6:['How a proof by mathematical induction is set up.','What it means for a set of connectives to be complete.','The difference between soundness and completeness.'],
  7:['Why universal claims pair with ⊃ and existential claims with &.','How quantifier order changes meaning.','How identity lets PLE count.'],
  8:['What an interpretation specifies.','Why one interpretation can show invalidity but not validity.','What a truth-functional expansion is for.'],
  9:['Why universals are never checked off.','The difference between ∃D and ∃D2.','Why some trees never end.'],
  10:['The restrictions on ∀I and ∃E, and what each one blocks.','When to start ∃E.','How =I and =E work.'],
  11:['How the completeness proof for PD extends the one for SD.','What a maximally consistent, ∃-complete set is.','What Löwenheim–Skolem says.']
};
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
/* The private claude.ai viewer can't show other sites in a frame, so there the video is a link. */
const canEmbed=/(^|\.)kevinjpatton\.com$|\.github\.io$|^localhost$|^127\.0\.0\.1$/.test(location.hostname);
function render(el,ch){
  const id=VIDEOS[ch],tips=WATCH_FOR[ch]||[];
  const url='https://www.youtube.com/watch?v='+id;
  let player;
  if(!id)player='<div class="vidsoon"><b>Video overview coming soon.</b><span>It will appear here once it\'s uploaded.</span></div>';
  else if(canEmbed)player='<div class="vidframe"><iframe src="https://www.youtube-nocookie.com/embed/'+esc(id)+'?rel=0" title="Chapter '+ch+' video overview" loading="lazy" allow="accelerometer; encrypted-media; gyroscope; picture-in-picture; fullscreen" allowfullscreen></iframe></div><p class="note"><a href="'+esc(url)+'" target="_blank" rel="noopener">Open on YouTube</a></p>';
  else player='<a class="vidlink" href="'+esc(url)+'" target="_blank" rel="noopener"><span class="vidplay" aria-hidden="true">▶</span><span><b>Watch the Chapter '+ch+' overview</b><span class="note">Opens on YouTube</span></span></a>';
  el.innerHTML='<div class="wrap"><div class="sec-head"><div class="eyebrow">Watch first</div><h2>Video overview</h2><p class="lede">A short overview of the chapter to watch before reading the notes below.</p></div>'+
    '<div class="vidgrid"><div class="stack">'+player+'</div>'+
    (tips.length?'<div class="side"><h3>Listen for</h3><ul class="bring">'+tips.map(t=>'<li>'+esc(t)+'</li>').join('')+'</ul></div>':'')+'</div></div>';
}
document.querySelectorAll('[data-video-chapter]').forEach(el=>render(el,+el.dataset.videoChapter));
/* home page: a link in the "Now reading" card when that chapter has a video */
document.querySelectorAll('[data-video-link]').forEach(el=>{const ch=+el.dataset.videoLink;if(VIDEOS[ch])el.innerHTML='<a href="chapter-'+ch+'.html#video">▶ Watch the overview</a>';});
window.VIDEOS=VIDEOS;
})();
