/* apply saved theme before first paint */
try{var _s=JSON.parse(localStorage.getItem('thewrongway.v1')||'null'),_l=!!(_s&&_s.settings&&_s.settings.theme==='light');if(_l){document.documentElement.setAttribute('data-theme','light');}}catch(e){}
/* browser UI colour: charcoal (or light), never the crawler-facing green */
try{document.getElementById('metaTheme').setAttribute('content',window._l?'#E7EBF0':'#090B0E');}catch(e){}

document.addEventListener('DOMContentLoaded', function(){
(function(){
'use strict';

/*LOGIC-START*/
/* =====================================================================
   PURE GAME LOGIC — seeded RNG, city generation, graph, Dijkstra, routes, scoring
   ===================================================================== */
var W=1000,H=700,SCALE=2.2; // SCALE: metres per map unit
var DIFF={
  easy:  {cols:7, rows:5, remove:.06,diag:0,  avenues:0,stubs:1,art:1,jitter:.14,warp:8, minHops:5, minFrac:.42},
  medium:{cols:10,rows:7, remove:.12,diag:.16,avenues:1,stubs:4,art:2,jitter:.17,warp:12,minHops:8, minFrac:.50},
  hard:  {cols:14,rows:10,remove:.15,diag:.22,avenues:2,stubs:9,art:3,jitter:.18,warp:14,minHops:13,minFrac:.55}
};
function hashString(s){var h=1779033703^s.length;for(var i=0;i<s.length;i++){h=Math.imul(h^s.charCodeAt(i),3432918353);h=h<<13|h>>>19;}
  h=Math.imul(h^h>>>16,2246822507);h=Math.imul(h^h>>>13,3266489909);return(h^h>>>16)>>>0;}
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;var t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
function clamp(v,a,b){return v<a?a:v>b?b:v;}

function MinHeap(){this.a=[];}
MinHeap.prototype.push=function(k,v){var a=this.a;a.push([k,v]);var i=a.length-1;while(i>0){var p=(i-1)>>1;if(a[p][0]<=a[i][0])break;var t=a[p];a[p]=a[i];a[i]=t;i=p;}};
MinHeap.prototype.pop=function(){var a=this.a,top=a[0],last=a.pop();if(a.length){a[0]=last;var i=0;for(;;){var l=2*i+1,r=l+1,m=i;if(l<a.length&&a[l][0]<a[m][0])m=l;if(r<a.length&&a[r][0]<a[m][0])m=r;if(m===i)break;var t=a[m];a[m]=a[i];a[i]=t;i=m;}}return top;};

function orient(ax,ay,bx,by,cx,cy){return (bx-ax)*(cy-ay)-(by-ay)*(cx-ax);}
function segsCross(a,b,c,d){
  var o1=orient(a.x,a.y,b.x,b.y,c.x,c.y),o2=orient(a.x,a.y,b.x,b.y,d.x,d.y),o3=orient(c.x,c.y,d.x,d.y,a.x,a.y),o4=orient(c.x,c.y,d.x,d.y,b.x,b.y);
  return ((o1>0&&o2<0)||(o1<0&&o2>0))&&((o3>0&&o4<0)||(o3<0&&o4>0));}
function pointSegDist(p,a,b){var dx=b.x-a.x,dy=b.y-a.y,l2=dx*dx+dy*dy,t=l2?((p.x-a.x)*dx+(p.y-a.y)*dy)/l2:0;t=clamp(t,0,1);return Math.hypot(p.x-(a.x+t*dx),p.y-(a.y+t*dy));}
function edgeKey(a,b){return a<b?a*10000+b:b*10000+a;}

function dijkstra(city,src){
  var n=city.nodes.length,dist=new Array(n).fill(Infinity),prev=new Array(n).fill(-1),hops=new Array(n).fill(0);
  dist[src]=0;var h=new MinHeap();h.push(0,src);
  while(h.a.length){var top=h.pop(),d=top[0],u=top[1];if(d>dist[u])continue;
    var nb=city.adj[u];for(var k=0;k<nb.length;k++){var to=nb[k].to,nd=d+nb[k].e.w;if(nd<dist[to]){dist[to]=nd;prev[to]=u;hops[to]=hops[u]+1;h.push(nd,to);}}}
  return {dist:dist,prev:prev,hops:hops};
}
function pathTo(prev,src,dst){var p=[],c=dst;while(c!==-1){p.push(c);if(c===src)break;c=prev[c];}p.reverse();return p[0]===src?p:null;}
function edgeBetween(city,a,b){return city.emap.get(edgeKey(a,b))||null;}

function tryGenerate(seed,diff){
  var P=DIFF[diff],rng=mulberry32(seed>>>0);
  var R=function(a,b){return a+(b-a)*rng();},RI=function(a,b){return Math.floor(R(a,b+1));};
  var cols=P.cols,rows=P.rows,mx=46,my=46,i,j;
  var cw=[],rh=[],sw=0,sh=0;
  for(i=0;i<cols-1;i++){var v=R(.72,1.32);cw.push(v);sw+=v;}
  for(j=0;j<rows-1;j++){var v2=R(.72,1.32);rh.push(v2);sh+=v2;}
  var xs=[mx],ys=[my];
  for(i=0;i<cols-1;i++)xs.push(xs[i]+cw[i]/sw*(W-2*mx));
  for(j=0;j<rows-1;j++)ys.push(ys[j]+rh[j]/sh*(H-2*my));
  var avx=(W-2*mx)/(cols-1),avy=(H-2*my)/(rows-1),p1=R(0,6.28),p2=R(0,6.28);
  var nodes=[];
  for(j=0;j<rows;j++)for(i=0;i<cols;i++){
    var x=xs[i]+(rng()*2-1)*P.jitter*avx,y=ys[j]+(rng()*2-1)*P.jitter*avy;
    x+=P.warp*Math.sin(ys[j]/120+p1);y+=P.warp*Math.sin(xs[i]/160+p2);
    nodes.push({id:nodes.length,x:clamp(x,22,W-22),y:clamp(y,22,H-22),gi:i,gj:j});
  }
  var id=function(a,b){return b*cols+a;};
  var emap=new Map(),nbr=nodes.map(function(){return new Set();});
  function addEdge(a,b,type){var k=edgeKey(a,b);if(emap.has(k))return null;var e={a:Math.min(a,b),b:Math.max(a,b),type:type};emap.set(k,e);nbr[a].add(b);nbr[b].add(a);return e;}
  function delEdge(e){emap.delete(edgeKey(e.a,e.b));nbr[e.a].delete(e.b);nbr[e.b].delete(e.a);}
  function connected(){var seen=new Uint8Array(nodes.length),st=[0],c=1;seen[0]=1;while(st.length){var u=st.pop();nbr[u].forEach(function(v){if(!seen[v]){seen[v]=1;c++;st.push(v);}});}return c===nodes.length;}

  var artRows=new Set(),artCols=new Set();
  while(artRows.size<Math.min(P.art,rows-2))artRows.add(RI(1,rows-2));
  while(artCols.size<Math.min(P.art,cols-2))artCols.add(RI(1,cols-2));
  for(j=0;j<rows;j++)for(i=0;i<cols;i++){
    if(i<cols-1)addEdge(id(i,j),id(i+1,j),artRows.has(j)?'arterial':'street');
    if(j<rows-1)addEdge(id(i,j),id(i,j+1),artCols.has(i)?'arterial':'street');
  }
  var used=new Set();
  for(var k=0;k<P.avenues;k++){
    var dj=rng()<.5?1:-1,ai=RI(0,Math.max(0,Math.floor(cols/3))),aj=dj===1?RI(0,Math.floor(rows/3)):RI(Math.ceil(rows*2/3)-1,rows-1);
    var steps=0,maxSteps=RI(Math.floor(cols*.5),cols-1);
    while(ai+1<cols&&aj+dj>=0&&aj+dj<rows&&steps<maxSteps){
      var ck=Math.min(aj,aj+dj)*cols+ai;if(used.has(ck))break;used.add(ck);
      addEdge(id(ai,aj),id(ai+1,aj+dj),'avenue');ai++;aj+=dj;steps++;
    }
  }
  if(P.diag>0)for(j=0;j<rows-1;j++)for(i=0;i<cols-1;i++){
    var ck2=j*cols+i;if(used.has(ck2))continue;
    if(rng()<P.diag){if(rng()<.5)addEdge(id(i,j),id(i+1,j+1),'diag');else addEdge(id(i+1,j),id(i,j+1),'diag');used.add(ck2);}
  }
  // remove some plain streets without disconnecting the network or creating accidental dead ends
  var cand=[];emap.forEach(function(e){if(e.type==='street')cand.push(e);});
  for(i=cand.length-1;i>0;i--){var r2=Math.floor(rng()*(i+1)),t=cand[i];cand[i]=cand[r2];cand[r2]=t;}
  for(i=0;i<cand.length;i++){var e=cand[i];
    if(rng()>=P.remove)continue;if(nbr[e.a].size<3||nbr[e.b].size<3)continue;
    delEdge(e);if(!connected()){emap.set(edgeKey(e.a,e.b),e);nbr[e.a].add(e.b);nbr[e.b].add(e.a);}
  }
  // dead-end stubs (cul-de-sacs)
  var placed=0,tries=0,stubbed=new Set(),gridN=cols*rows;
  while(placed<P.stubs&&tries<120){tries++;
    var n=nodes[RI(0,gridN-1)];if(stubbed.has(n.id))continue;
    var ci=n.gi-(rng()<.5?1:0),cj=n.gj-(rng()<.5?1:0);
    if(ci<0||cj<0||ci>=cols-1||cj>=rows-1||used.has(cj*cols+ci))continue;
    var cc=[nodes[id(ci,cj)],nodes[id(ci+1,cj)],nodes[id(ci+1,cj+1)],nodes[id(ci,cj+1)]];
    var cx=(cc[0].x+cc[1].x+cc[2].x+cc[3].x)/4,cy=(cc[0].y+cc[1].y+cc[2].y+cc[3].y)/4,tt=R(.4,.58);
    var p={x:n.x+(cx-n.x)*tt,y:n.y+(cy-n.y)*tt},ok=true,m;
    for(m=0;m<nodes.length&&ok;m++){if(nodes[m].id!==n.id&&Math.hypot(nodes[m].x-p.x,nodes[m].y-p.y)<20)ok=false;}
    if(ok){emap.forEach(function(e2){if(!ok)return;var A=nodes[e2.a],B=nodes[e2.b];
      if(pointSegDist(p,A,B)<10)ok=false;else if(e2.a!==n.id&&e2.b!==n.id&&segsCross(n,p,A,B))ok=false;});}
    if(!ok)continue;
    var nn={id:nodes.length,x:p.x,y:p.y,gi:-1,gj:-1,stub:true};nodes.push(nn);nbr.push(new Set());
    addEdge(n.id,nn.id,'stub');stubbed.add(n.id);used.add(cj*cols+ci);placed++;
  }
  // finalise edges and verify geometry matches graph (no crossings / no near-touching roads)
  var el=[];emap.forEach(function(e){el.push(e);});
  el.sort(function(a,b){return a.a-b.a||a.b-b.b;});
  for(i=0;i<el.length;i++)for(j=i+1;j<el.length;j++){var e1=el[i],e2b=el[j];
    if(e1.a===e2b.a||e1.a===e2b.b||e1.b===e2b.a||e1.b===e2b.b)continue;
    if(segsCross(nodes[e1.a],nodes[e1.b],nodes[e2b.a],nodes[e2b.b]))return null;}
  for(i=0;i<nodes.length;i++)for(j=0;j<el.length;j++){var ee=el[j];if(ee.a===i||ee.b===i)continue;if(pointSegDist(nodes[i],nodes[ee.a],nodes[ee.b])<4)return null;}
  var adj=nodes.map(function(){return [];}),edges=[];
  el.forEach(function(e,idx){var A=nodes[e.a],B=nodes[e.b],len=Math.hypot(A.x-B.x,A.y-B.y);
    var edge={id:idx,a:e.a,b:e.b,type:e.type,len:len,w:Math.max(1,Math.round(len*SCALE))};
    edges.push(edge);adj[e.a].push({to:e.b,e:edge});adj[e.b].push({to:e.a,e:edge});});
  var em=new Map();edges.forEach(function(e){em.set(edgeKey(e.a,e.b),e);});
  var city={seed:seed,diff:diff,W:W,H:H,cols:cols,rows:rows,nodes:nodes,edges:edges,adj:adj,emap:em,start:-1,end:-1,optimal:null};
  // choose start & finish
  var elig=nodes.filter(function(q){return !q.stub&&adj[q.id].length>=2&&q.x>=56&&q.x<=W-56;});
  var diagLen=Math.hypot(W,H),best=null,attempt;
  for(attempt=0;attempt<150&&!best;attempt++){
    var s=elig[RI(0,elig.length-1)],D=dijkstra(city,s.id);
    var cs=elig.filter(function(q){return q.id!==s.id&&Math.hypot(q.x-s.x,q.y-s.y)>=P.minFrac*diagLen&&D.hops[q.id]>=P.minHops&&D.dist[q.id]<Infinity;});
    if(cs.length){var q2=cs[RI(0,cs.length-1)];best={s:s.id,e:q2.id};}
  }
  if(!best){var s0=elig[0],D0=dijkstra(city,s0.id),far=-1,fd=-1;
    elig.forEach(function(q){if(D0.dist[q.id]<Infinity&&D0.dist[q.id]>fd){fd=D0.dist[q.id];far=q.id;}});
    if(far<0||far===s0.id)return null;best={s:s0.id,e:far};}
  city.start=best.s;city.end=best.e;
  var DD=dijkstra(city,city.start),pp=pathTo(DD.prev,city.start,city.end);
  if(!pp||pp.length<2||!isFinite(DD.dist[city.end]))return null;
  city.optimal={dist:DD.dist[city.end],path:pp};
  return city;
}
function generateCity(seed,diff){
  for(var k=0;k<24;k++){var c=tryGenerate((seed+k*7919)>>>0,diff);if(c){c.seed=seed;c.variant=k;return c;}}
  throw new Error('city generation failed');
}

/* ---- route helpers ---- */
function routeDistance(city,path){var d=0;for(var i=1;i<path.length;i++){var e=edgeBetween(city,path[i-1],path[i]);if(!e)return NaN;d+=e.w;}return d;}
function routeTurns(city,path){var t=0;for(var i=1;i<path.length-1;i++){var a=city.nodes[path[i-1]],b=city.nodes[path[i]],c=city.nodes[path[i+1]];
  var a1=Math.atan2(b.y-a.y,b.x-a.x),a2=Math.atan2(c.y-b.y,c.x-b.x),d=Math.abs(a2-a1);if(d>Math.PI)d=2*Math.PI-d;if(d>Math.PI/6)t++;}return t;}
function routeJunctions(city,path){var j=0;for(var i=1;i<path.length-1;i++)if(city.adj[path[i]].length>=3)j++;return j;}
function validateRoute(city,path){
  if(!path||path.length<2)return {ok:false,msg:'Draw a route first. Start from the green A pin and follow the streets.'};
  if(path[0]!==city.start)return {ok:false,msg:'A route must begin at the green A pin.'};
  var seen=new Set();
  for(var i=0;i<path.length;i++){if(seen.has(path[i]))return {ok:false,msg:'Your route crosses itself.'};seen.add(path[i]);
    if(i>0&&!edgeBetween(city,path[i-1],path[i]))return {ok:false,msg:'Your route uses a road that does not exist.'};}
  if(path[path.length-1]!==city.end)return {ok:false,msg:"Your route hasn't reached B yet. Keep going from the glowing junction."};
  return {ok:true};
}
function resultLabel(eff){return eff>=0.9999?'Perfect route':eff>=0.92?'Close enough':eff>=0.8?'Solid driving':eff>=0.6?'Took the scenic route':eff>=0.4?'Lost the plot':'Definitely the wrong way';}
function scoreRoute(city,path){
  var dist=routeDistance(city,path),opt=city.optimal.dist;
  var exact=dist<=opt?1:clamp(opt/dist,0,1);
  return {dist:dist,opt:opt,extra:Math.max(0,dist-opt),exact:exact,eff:Math.round(exact*1000)/10,points:Math.round(1000*exact*exact),
    turns:routeTurns(city,path),junctions:routeJunctions(city,path),label:resultLabel(exact)};
}
/*LOGIC-END*/

/* =====================================================================
   STORAGE
   ===================================================================== */
var STORE_KEY='thewrongway.v1',storageOK=true;
function defaults(){return {v:1,settings:{theme:'dark',practiceDiff:'medium',hints:true,buildings:true,motion:'auto',sound:false,volume:0.7},daily:{},
  practice:{completed:0,totalEff:0,totalPoints:0,bestEff:0,bestScore:0,perfect:0,byDiff:{easy:0,medium:0,hard:0}}};}
function num(v,d){v=Number(v);return isFinite(v)?v:d;}
function sanitize(o){
  var d=defaults();if(!o||typeof o!=='object')return d;
  var s=o.settings||{};
  d.settings.theme=s.theme==='light'?'light':'dark';
  d.settings.practiceDiff=DIFF[s.practiceDiff]?s.practiceDiff:'medium';
  d.settings.hints=s.hints!==false;d.settings.buildings=s.buildings!==false;
  d.settings.motion=(s.motion==='on'||s.motion==='off')?s.motion:'auto';
  d.settings.sound=s.sound===true;                                  /* sound is opt-in: only an explicit true enables it */
  d.settings.volume=Math.round(clamp(num(s.volume,0.7),0,1)*100)/100;
  if(o.daily&&typeof o.daily==='object'){Object.keys(o.daily).forEach(function(k){
    var r=o.daily[k];if(!/^\d{4}-\d{2}-\d{2}$/.test(k)||!r||typeof r!=='object')return;
    if(!Array.isArray(r.path)||!r.path.every(function(x){return Number.isInteger(x)&&x>=0;}))return;
    d.daily[k]={seed:num(r.seed,0)>>>0,diff:DIFF[r.diff]?r.diff:'medium',path:r.path,dist:num(r.dist,0),opt:num(r.opt,0),eff:clamp(num(r.eff,0),0,100),points:clamp(Math.round(num(r.points,0)),0,1000),turns:num(r.turns,0)};});}
  var p=o.practice||{};
  d.practice.completed=Math.max(0,Math.floor(num(p.completed,0)));d.practice.totalEff=Math.max(0,num(p.totalEff,0));d.practice.totalPoints=Math.max(0,num(p.totalPoints,0));
  d.practice.bestEff=clamp(num(p.bestEff,0),0,100);d.practice.bestScore=clamp(num(p.bestScore,0),0,1000);d.practice.perfect=Math.max(0,Math.floor(num(p.perfect,0)));
  var b=p.byDiff||{};['easy','medium','hard'].forEach(function(k){d.practice.byDiff[k]=Math.max(0,Math.floor(num(b[k],0)));});
  return d;
}
var S=(function(){try{var raw=localStorage.getItem(STORE_KEY);return raw?sanitize(JSON.parse(raw)):defaults();}catch(e){storageOK=false;return defaults();}})();
function save(){try{localStorage.setItem(STORE_KEY,JSON.stringify(S));}catch(e){storageOK=false;}}

/* =====================================================================
   SOUND — small Web Audio synth. No files, no libraries.
   - Opt-in: S.settings.sound is false until the player switches it on.
   - Nothing is created until a real user gesture (autoplay policy), and never while sound is off.
   - Every call is wrapped so a missing/blocked audio device can never break gameplay.
   ===================================================================== */
var Sound=(function(){
  var AC=window.AudioContext||window.webkitAudioContext;
  var supported=!!AC,broken=false,ctx=null,master=null,noiseBuf=null,lastAt={},stamps=[];
  var SPEC={ /* gap = min ms between repeats of the same sound; pri = bypasses the global rate guard */
    snap:{gap:70},undo:{gap:80},clear:{gap:160},error:{gap:300},tap:{gap:60},confirm:{gap:200},modal:{gap:150},
    arrive:{gap:150,pri:1},submit:{pri:1},optimal:{pri:1},on:{pri:1},off:{pri:1}
  };
  function enabled(){return supported&&!broken&&S.settings.sound===true;}
  function level(){var v=clamp(num(S.settings.volume,0.7),0,1);return v*v;} /* squared = more natural slider feel */
  function build(){
    try{ctx=new AC({latencyHint:'interactive'});}catch(e){try{ctx=new AC();}catch(e2){ctx=null;broken=true;return false;}}
    master=ctx.createGain();master.gain.value=level();
    var lim=ctx.createDynamicsCompressor(); /* gentle safety limiter so layered sounds can never spike */
    lim.threshold.value=-16;lim.knee.value=12;lim.ratio.value=8;lim.attack.value=.003;lim.release.value=.18;
    master.connect(lim);lim.connect(ctx.destination);
    var n=Math.floor(ctx.sampleRate*.4),b=ctx.createBuffer(1,n,ctx.sampleRate),d=b.getChannelData(0);
    for(var i=0;i<n;i++)d[i]=Math.random()*2-1;
    noiseBuf=b;return true;
  }
  /* Call from a user-gesture handler. Resolves true once audio is running. */
  function unlock(){
    if(!enabled())return Promise.resolve(false);
    try{
      if(!ctx&&!build())return Promise.resolve(false);
      if(ctx.state==='running')return Promise.resolve(true);
      var p=ctx.resume();
      return Promise.resolve(p).then(function(){return ctx.state==='running';},function(){return false;});
    }catch(e){broken=true;return Promise.resolve(false);}
  }
  function setVolume(){try{if(ctx&&master)master.gain.setTargetAtTime(level(),ctx.currentTime,.015);}catch(e){}}
  function sync(){try{if(!ctx)return;setVolume();if(!enabled()&&ctx.state==='running')ctx.suspend();}catch(e){}}

  /* ---- synthesis primitives ---- */
  function env(g,t,a,d,v){g.gain.setValueAtTime(.0001,t);g.gain.exponentialRampToValueAtTime(Math.max(.0002,v),t+a);g.gain.exponentialRampToValueAtTime(.0001,t+a+d);}
  function tone(t,o){
    var osc=ctx.createOscillator(),g=ctx.createGain(),a=o.a||.002,d=o.d||.08,j=o.j||1,lp=null;
    osc.type=o.type||'sine';osc.frequency.setValueAtTime(o.f*j,t);
    if(o.to)osc.frequency.exponentialRampToValueAtTime(o.to*j,t+a+d);
    env(g,t,a,d,o.v);osc.connect(g);
    if(o.lp){lp=ctx.createBiquadFilter();lp.type='lowpass';lp.frequency.value=o.lp;g.connect(lp);lp.connect(o.dst||master);}else g.connect(o.dst||master);
    osc.start(t);osc.stop(t+a+d+.04);
    osc.onended=function(){try{osc.disconnect();g.disconnect();if(lp)lp.disconnect();}catch(e){}};
  }
  function noise(t,o){
    var src=ctx.createBufferSource(),bp=ctx.createBiquadFilter(),g=ctx.createGain(),a=o.a||.003,d=o.d||.1;
    src.buffer=noiseBuf;bp.type=o.type||'bandpass';bp.Q.value=o.q||1;
    bp.frequency.setValueAtTime(o.f,t);if(o.to)bp.frequency.exponentialRampToValueAtTime(o.to,t+a+d);
    env(g,t,a,d,o.v);src.connect(bp);bp.connect(g);g.connect(o.dst||master);
    src.start(t,Math.random()*.12);src.stop(t+a+d+.04);
    src.onended=function(){try{src.disconnect();bp.disconnect();g.disconnect();}catch(e){}};
  }
  function echo(life){ /* short feedback delay, used only for the optimal-route reward */
    var inp=ctx.createGain(),dl=ctx.createDelay(.5),fb=ctx.createGain(),wet=ctx.createGain();
    dl.delayTime.value=.14;fb.gain.value=.3;wet.gain.value=.45;
    inp.connect(master);inp.connect(dl);dl.connect(fb);fb.connect(dl);dl.connect(wet);wet.connect(master);
    setTimeout(function(){try{inp.disconnect();dl.disconnect();fb.disconnect();wet.disconnect();}catch(e){}},(life+.6)*1000);
    return inp;
  }

  /* ---- the sounds (all well under half a second except the optimal-route reward) ---- */
  var FX={
    snap:function(t,j){ /* light tick + soft wooden body */
      tone(t,{f:1500,to:1050,type:'triangle',a:.001,d:.03,v:.23,j:j});
      tone(t,{f:520,to:360,a:.001,d:.055,v:.2,j:j});
    },
    arrive:function(t){ /* reached B: two soft rising notes */
      tone(t,{f:880,type:'triangle',a:.004,d:.16,v:.12});
      tone(t+.07,{f:1318.5,type:'triangle',a:.004,d:.22,v:.12});
      tone(t+.07,{f:2637,a:.004,d:.12,v:.035});
    },
    undo:function(t,j){ /* quick downward blip */
      tone(t,{f:760,to:430,a:.002,d:.09,v:.21,j:j});
      tone(t,{f:1100,to:800,type:'triangle',a:.001,d:.02,v:.07,j:j});
    },
    clear:function(t){ /* soft downward sweep + low thud */
      noise(t,{f:2600,to:450,q:.9,a:.004,d:.17,v:.18});
      tone(t,{f:260,to:120,a:.003,d:.13,v:.21});
    },
    error:function(t){ /* two muted low blips */
      tone(t,{f:190,to:150,type:'triangle',a:.003,d:.1,v:.14,lp:900});
      tone(t+.1,{f:160,to:125,type:'triangle',a:.003,d:.12,v:.12,lp:900});
    },
    submit:function(t){ /* confirmation: E5 then B5 */
      tone(t,{f:659.25,type:'triangle',a:.003,d:.15,v:.15});
      tone(t,{f:659.25,a:.003,d:.15,v:.08});
      tone(t+.09,{f:987.77,type:'triangle',a:.003,d:.24,v:.17});
      tone(t+.09,{f:987.77,a:.003,d:.24,v:.09});
    },
    optimal:function(t){ /* rising pentatonic arpeggio into a bright chord, with a little echo and sparkle */
      var bus=echo(1.4),n=[523.25,659.25,783.99,1046.5,1318.5],i;
      for(i=0;i<n.length;i++){
        tone(t+i*.075,{f:n[i],type:'triangle',a:.004,d:.2,v:.13,dst:bus});
        tone(t+i*.075,{f:n[i]*2,a:.004,d:.14,v:.04,dst:bus});
      }
      var c=t+n.length*.075;
      [1046.5,1318.5,1568].forEach(function(f){tone(c,{f:f,type:'triangle',a:.006,d:.8,v:.1,dst:bus});tone(c,{f:f/2,a:.006,d:.8,v:.05,dst:bus});});
      noise(t+.28,{type:'highpass',f:6500,a:.01,d:.2,v:.03,dst:bus});
    },
    tap:function(t,j){ /* interface tick */
      tone(t,{f:1000,to:780,a:.001,d:.03,v:.18,j:j});
      tone(t,{f:2000,type:'triangle',a:.001,d:.012,v:.05,j:j});
    },
    on:function(t){tone(t,{f:620,a:.003,d:.1,v:.12});tone(t+.075,{f:930,a:.003,d:.16,v:.12});},
    off:function(t){tone(t,{f:930,a:.003,d:.1,v:.1});tone(t+.075,{f:620,a:.003,d:.14,v:.1});},
    confirm:function(t){tone(t,{f:988,a:.003,d:.14,v:.11});tone(t+.06,{f:1319,a:.003,d:.16,v:.08});},
    modal:function(t){tone(t,{f:420,to:560,a:.002,d:.07,v:.18});}
  };

  /* Rate guard: same-sound gaps, never two sounds in one frame, at most 8 per second.
     Priority sounds (submit, optimal, arrive, on/off) always play. */
  function allow(name,now){
    var sp=SPEC[name];if(!sp)return false;
    if(sp.gap&&now-(lastAt[name]||-1e9)<sp.gap)return false;
    stamps=stamps.filter(function(x){return now-x<1000;});
    if(!sp.pri){
      if(stamps.length&&now-stamps[stamps.length-1]<24)return false;
      if(stamps.length>=8)return false;
    }
    lastAt[name]=now;stamps.push(now);return true;
  }
  function fire(name){
    var j=1+(Math.random()*2-1)*.025;
    FX[name](ctx.currentTime+.006,j);
  }
  function play(name,opt){
    try{
      var force=!!(opt&&opt.force);
      if(!ctx||!FX[name]||!(force||enabled()))return;
      var now=performance.now();
      if(!allow(name,now))return;
      if(ctx.state==='running'){fire(name);return;}
      /* Suspended (idle tab, iOS interruption): try to wake it, and only play if that happens right away.
         Never schedule while suspended, or sounds would pile up and fire together on resume. */
      Promise.resolve(ctx.resume()).then(function(){if(ctx.state==='running'&&performance.now()-now<250)fire(name);},function(){});
    }catch(e){}
  }
  document.addEventListener('visibilitychange',function(){try{if(document.hidden&&ctx&&ctx.state==='running')ctx.suspend();}catch(e){}});
  return {supported:supported,unlock:unlock,play:play,setVolume:setVolume,sync:sync};
})();
/* A real gesture is the only thing that ever creates/resumes the audio context (and only if sound is on). */
['pointerdown','pointerup','touchend','keydown','click'].forEach(function(ev){
  document.addEventListener(ev,function(){Sound.unlock();},{capture:true,passive:true});
});
/* Generic interface tick for buttons. Buttons with their own sound are marked data-snd="none". */
document.addEventListener('click',function(e){
  var b=e.target&&e.target.closest?e.target.closest('button'):null;
  if(!b||b.disabled||b.dataset.snd==='none')return;
  Sound.play('tap');
},true);

/* =====================================================================
   HELPERS
   ===================================================================== */
function $(id){return document.getElementById(id);}
function f(n){return n.toFixed(1);}
function fmtM(n){return Math.round(n).toLocaleString('en-GB')+' m';}
var DIFF_LABEL={easy:'Easy',medium:'Medium',hard:'Hard'};
function pad2(n){return (n<10?'0':'')+n;}
function dateKey(d){d=d||new Date();return d.getFullYear()+'-'+pad2(d.getMonth()+1)+'-'+pad2(d.getDate());}
function dailyDifficulty(key){var p=key.split('-').map(Number);var dayNum=Math.floor(Date.UTC(p[0],p[1]-1,p[2])/86400000);return ['medium','easy','hard'][((dayNum%3)+3)%3];}
function prettyDate(d){return (d||new Date()).toLocaleDateString('en-GB',{weekday:'short',day:'numeric',month:'short'}).toUpperCase().replace(/,/g,'');}
function reduceMotion(){var m=S.settings.motion;if(m==='on')return true;if(m==='off')return false;return !!(window.matchMedia&&matchMedia('(prefers-reduced-motion: reduce)').matches);}
function applyMotion(){var rm=reduceMotion();document.documentElement.classList.toggle('rm',rm);document.documentElement.classList.toggle('rm-off',S.settings.motion==='off');}
function applyTheme(){document.documentElement.setAttribute('data-theme',S.settings.theme);var m=$('metaTheme');if(m)m.setAttribute('content',S.settings.theme==='light'?'#E7EBF0':'#090B0E');}
function sleep(ms,tok){return new Promise(function(r){setTimeout(function(){r(tok===G.anim);},ms);});}
function tween(ms,fn,tok){return new Promise(function(res){var t0=performance.now();(function step(t){if(tok!==G.anim)return res(false);var p=Math.min(1,(t-t0)/ms);fn(p);if(p<1)requestAnimationFrame(step);else res(true);})(t0);});}
function ease(p){return p<.5?4*p*p*p:1-Math.pow(-2*p+2,3)/2;}

/* =====================================================================
   STATE
   ===================================================================== */
var G={view:'home',nav:'home',mode:'daily',diff:'medium',city:null,seed:0,dateKey:'',route:[],locked:false,result:null,review:false,counted:true,anim:0,u:1,refs:null,drag:null,hover:null,toastT:0};
var svg=$('mapSvg');

/* =====================================================================
   MAP RENDERING
   ===================================================================== */
function markerHTML(kind,node){
  var color=kind==='A'?'var(--start)':'var(--end)',label=kind==='A'?'START':'FINISH',flip=node.y<96,cy=flip?32:-32;
  var right=node.x<W-170,pw=kind==='A'?58:68,px=right?26:-26-pw;
  var pin=flip?'M0 0C-4 8-17 16-17 29A17 17 0 1 0 17 29C17 16 4 8 0 0Z':'M0 0C-4-8-17-16-17-29A17 17 0 1 1 17-29C17-16 4-8 0 0Z';
  return '<g class="mk" data-x="'+f(node.x)+'" data-y="'+f(node.y)+'" style="--c:'+color+'">'+
    '<circle class="mk-ring" r="13" stroke="'+color+'"/>'+
    '<g class="mk-pin"><path d="'+pin+'" fill="'+color+'" stroke="var(--map-bg)" stroke-width="2"/>'+
    '<text class="mk-letter" x="0" y="'+cy+'">'+kind+'</text></g>'+
    '<rect class="mk-pill" x="'+px+'" y="'+(cy-11)+'" width="'+pw+'" height="22" rx="11"/>'+
    '<text class="mk-text" x="'+(px+pw/2)+'" y="'+cy+'" text-anchor="middle">'+label+'</text></g>';
}
function buildMapSVG(el,city,o){
  var N=city.nodes,p=[],cols=city.cols;
  function has(a,b){return city.emap.has(edgeKey(a,b));}
  function inset(P){var cx=0,cy=0;P.forEach(function(q){cx+=q.x;cy+=q.y;});cx/=P.length;cy/=P.length;return P.map(function(q){return {x:cx+(q.x-cx)*.88,y:cy+(q.y-cy)*.88};});}
  function poly(P){return 'M'+P.map(function(q){return f(q.x)+' '+f(q.y);}).join('L')+'Z';}
  var rd=mulberry32((city.seed^0x9E3779B9)>>>0),blocks=[],parks=[],blds=[];
  for(var j=0;j<city.rows-1;j++)for(var i=0;i<cols-1;i++){
    var a=j*cols+i,b=a+1,c=a+cols+1,d=a+cols;
    if(!(has(a,b)&&has(b,c)&&has(d,c)&&has(a,d)))continue;
    var A=N[a],B=N[b],C=N[c],D=N[d];
    if(has(a,c)){blocks.push(poly(inset([A,B,C])),poly(inset([A,C,D])));continue;}
    if(has(b,d)){blocks.push(poly(inset([A,B,D])),poly(inset([B,C,D])));continue;}
    var park=rd()<.08;
    (park?parks:blocks).push(poly(inset([A,B,C,D])));
    for(var sa=0;sa<2;sa++)for(var sb=0;sb<2;sb++){
      var skip=rd()<.28,u0=sa*.5+.14+rd()*.07,u1=sa*.5+.5-.06-rd()*.07,v0=sb*.5+.14+rd()*.07,v1=sb*.5+.5-.06-rd()*.07;
      if(skip||park||!o.buildings)continue;
      var bil=function(u,v){return {x:(1-u)*(1-v)*A.x+u*(1-v)*B.x+u*v*C.x+(1-u)*v*D.x,y:(1-u)*(1-v)*A.y+u*(1-v)*B.y+u*v*C.y+(1-u)*v*D.y};};
      blds.push(poly([bil(u0,v0),bil(u1,v0),bil(u1,v1),bil(u0,v1)]));
    }
  }
  p.push('<rect class="m-bg" x="0" y="0" width="'+W+'" height="'+H+'"/>');
  p.push('<g class="l-blocks"><path class="blk" d="'+blocks.join('')+'"/><path class="park" d="'+parks.join('')+'"/><path class="bld" d="'+blds.join('')+'"/></g>');
  var dS=[],dM=[];
  city.edges.forEach(function(e){var A=N[e.a],B=N[e.b],s='M'+f(A.x)+' '+f(A.y)+'L'+f(B.x)+' '+f(B.y);(e.type==='arterial'||e.type==='avenue'?dM:dS).push(s);});
  p.push('<g class="l-roads"><path class="rd" d="'+dS.join('')+'"/><path class="rd-main" d="'+dM.join('')+'"/><path class="rd-mid" d="'+dM.join('')+'"/></g>');
  var nd='';N.forEach(function(q){var dg=city.adj[q.id].length;nd+='<circle class="nd '+(dg===1?'nd1':dg===2?'nd2':'nd3')+'" cx="'+f(q.x)+'" cy="'+f(q.y)+'" r="3"/>';});
  p.push('<g class="l-nodes">'+nd+'</g>');
  p.push('<g class="l-opt"><path class="opt-glow" pathLength="1000" d=""/><path class="opt" pathLength="1000" d=""/></g>');
  p.push('<g class="l-route"><path class="route-glow" d=""/><path class="route-main" d=""/><path class="route-last" d=""/></g>');
  p.push('<path class="hover-seg" d=""/><g class="l-hints"></g><g class="l-end"></g>');
  p.push('<g class="l-car" style="display:none"><rect class="car-body" x="-12" y="-6" width="24" height="12" rx="4.5"/><rect class="car-glass" x="1" y="-4.2" width="6.5" height="8.4" rx="1.6"/></g>');
  p.push('<g class="l-markers" pointer-events="none">'+markerHTML('A',N[city.start])+markerHTML('B',N[city.end])+'</g>');
  el.innerHTML=p.join('');
}
function applyScale(el){
  var w=el.getBoundingClientRect().width||W,u=W/w;
  el.style.setProperty('--u',u.toFixed(4));
  var cs=el.querySelectorAll('.nd');
  for(var i=0;i<cs.length;i++){var c=cs[i];c.setAttribute('r',((c.classList.contains('nd1')?3.6:c.classList.contains('nd2')?2.3:3.2)*u).toFixed(2));}
  var m=clamp(u*.95,1,2.1),mk=el.querySelectorAll('.mk');
  for(var k=0;k<mk.length;k++)mk[k].setAttribute('transform','translate('+mk[k].dataset.x+' '+mk[k].dataset.y+') scale('+m.toFixed(3)+')');
  var car=el.querySelector('.l-car');if(car)car.dataset.m=clamp(u*.9,1,2).toFixed(3);
  return u;
}
function grabRefs(){var q=function(s){return svg.querySelector(s);};
  G.refs={glow:q('.route-glow'),main:q('.route-main'),last:q('.route-last'),hover:q('.hover-seg'),hints:q('.l-hints'),end:q('.l-end'),opt:q('.opt'),optGlow:q('.opt-glow'),car:q('.l-car')};}

/* =====================================================================
   ROUTE DRAWING
   ===================================================================== */
function pathD(ids){var N=G.city.nodes;return ids.length<2?'':'M'+ids.map(function(i){return f(N[i].x)+' '+f(N[i].y);}).join('L');}
function renderRoute(animLast){
  var c=G.city,R=G.route,r=G.refs,u=G.u,N=c.nodes,endId=R[R.length-1];
  r.glow.setAttribute('d',pathD(R));
  r.main.setAttribute('d',pathD(R.slice(0,-1)));
  var ld=R.length>=2?pathD(R.slice(-2)):'';
  r.last.setAttribute('d',ld);r.last.style.strokeDasharray='';
  if(animLast&&ld&&!reduceMotion()&&r.last.animate){
    var L=r.last.getTotalLength();r.last.style.strokeDasharray=L+' '+L;
    var an=r.last.animate([{strokeDashoffset:L},{strokeDashoffset:0}],{duration:170,easing:'ease-out'});
    an.onfinish=function(){r.last.style.strokeDasharray='';};
  }
  var e=N[endId];
  r.end.innerHTML=G.locked?'':'<circle class="end-ring" cx="'+f(e.x)+'" cy="'+f(e.y)+'" r="'+f(9*u)+'"/>';
  var h='';
  if(!G.locked&&endId!==c.end&&S.settings.hints){c.adj[endId].forEach(function(nb){if(R.indexOf(nb.to)>=0)return;var q=N[nb.to];h+='<circle class="hint" cx="'+f(q.x)+'" cy="'+f(q.y)+'" r="'+f(6.5*u)+'"/>';});}
  r.hints.innerHTML=h;
}
function setOdo(v){
  var box=$('odo');v=clamp(Math.round(v),0,99999);var s=String(v).padStart(5,'0');
  if(!box.children.length){for(var i=0;i<5;i++){var d=document.createElement('span');d.className='d';d.textContent='0';box.appendChild(d);}var un=document.createElement('span');un.className='unit';un.textContent='M';box.appendChild(un);}
  for(var k=0;k<5;k++){var el=box.children[k];if(el.textContent!==s[k]){el.textContent=s[k];el.classList.remove('tick');void el.offsetWidth;if(!reduceMotion())el.classList.add('tick');}}
  box.setAttribute('aria-label','Distance '+v+' metres');
}
function updateHUD(){
  var c=G.city,R=G.route,atB=R[R.length-1]===c.end;
  setOdo(routeDistance(c,R));$('hTurns').textContent=routeTurns(c,R);$('hJunc').textContent=routeJunctions(c,R);
  $('hStatus').textContent=R.length===1?'AT START':atB?'REACHED B':'EN ROUTE';
  $('undoBtn').disabled=G.locked||R.length<=1;$('clearBtn').disabled=G.locked||R.length<=1;
  $('resetBtn').disabled=G.locked;$('submitBtn').disabled=G.locked;$('submitBtn').classList.toggle('ready',atB&&!G.locked);
}
function toast(msg,kind){var t=$('toast');t.textContent=msg;t.className='toast show '+(kind||'info');clearTimeout(G.toastT);G.toastT=setTimeout(function(){t.classList.remove('show');},kind==='error'?3800:2800);}
function refresh(animLast){renderRoute(animLast);updateHUD();}

function tryAdd(id,silent){
  if(G.locked)return 'locked';
  var c=G.city,R=G.route,end=R[R.length-1];
  if(id===end)return 'same';
  if(R.length>1&&id===R[R.length-2]){R.pop();refresh(false);Sound.play('undo');return 'back';}
  if(!edgeBetween(c,end,id)){if(!silent){toast("That junction isn't connected to your position. Pick a ringed intersection.",'error');Sound.play('error');}return 'invalid';}
  if(end===c.end){if(!silent){toast("You've reached B. Submit your route, or undo to change it.",'good');Sound.play('tap');}return 'done';}
  if(R.indexOf(id)>=0){if(!silent){toast("Your route can't cross itself. Undo to back up first.",'error');Sound.play('error');}return 'loop';}
  R.push(id);refresh(true);
  if(id===c.end){toast("You've reached B! Submit your route when you're ready.",'good');Sound.play('arrive');}
  else Sound.play('snap');
  return 'added';
}
function undo(){if(G.locked||G.route.length<=1)return false;G.route.pop();refresh(false);Sound.play('undo');return true;}
function clearRoute(){if(G.locked||G.route.length<=1)return;G.route=[G.city.start];refresh(false);Sound.play('clear');toast('Route cleared. Start again from A.','info');}
async function resetBoard(){
  if(G.review||G.locked)return;
  if(G.route.length-1>=3){var ok=await confirmBox('Reset this challenge?','Your drawn route will be removed. The map and its pins stay exactly the same.','Reset');if(!ok)return;}
  G.route=[G.city.start];G.hover=null;G.refs.hover.setAttribute('d','');refresh(false);Sound.play('clear');toast('Challenge reset.','info');
}

/* pointer input */
function svgPt(ev){var p=svg.createSVGPoint();p.x=ev.clientX;p.y=ev.clientY;var m=svg.getScreenCTM();return m?p.matrixTransform(m.inverse()):{x:0,y:0};}
function nearest(p,radius,filter){var best=-1,bd=radius,N=G.city.nodes;for(var i=0;i<N.length;i++){if(filter&&!filter(i))continue;var d=Math.hypot(N[i].x-p.x,N[i].y-p.y);if(d<bd){bd=d;best=i;}}return best;}
function legalSet(){var R=G.route,end=R[R.length-1],s=new Set([end]);if(R.length>1)s.add(R[R.length-2]);G.city.adj[end].forEach(function(nb){s.add(nb.to);});return s;}
function clickAt(p){
  var rc=Math.max(26,30*G.u),legal=legalSet();
  var id=nearest(p,rc,function(i){return legal.has(i);});
  if(id>=0){tryAdd(id,false);return;}
  var any=nearest(p,Math.max(18,22*G.u));
  if(any>=0)tryAdd(any,false);
}
function dragStep(q){
  var rd=Math.max(14,16*G.u),id=nearest(q,rd);if(id<0)return;
  var end=G.route[G.route.length-1];if(id===end)return;
  if(legalSet().has(id))tryAdd(id,true);
}
function dragTo(p){
  var a=G.drag.last,dx=p.x-a.x,dy=p.y-a.y,dist=Math.hypot(dx,dy),step=Math.max(4,Math.max(14,16*G.u)*.5),n=Math.max(1,Math.ceil(dist/step));
  for(var k=1;k<=n&&!G.locked;k++)dragStep({x:a.x+dx*k/n,y:a.y+dy*k/n});
  G.drag.last=p;
}
function hoverAt(p){
  if(G.locked||!G.refs)return;
  var legal=legalSet(),R=G.route,end=R[R.length-1],N=G.city.nodes;
  var id=nearest(p,Math.max(26,30*G.u),function(i){return i!==end&&legal.has(i)&&R.indexOf(i)<0;});
  G.refs.hover.setAttribute('d',id>=0&&end!==G.city.end?'M'+f(N[end].x)+' '+f(N[end].y)+'L'+f(N[id].x)+' '+f(N[id].y):'');
  svg.style.cursor=id>=0?'pointer':'crosshair';
}
svg.addEventListener('pointerdown',function(ev){
  if(G.locked||G.view!=='game'||(ev.pointerType==='mouse'&&ev.button!==0))return;
  ev.preventDefault();try{svg.setPointerCapture(ev.pointerId);}catch(e){}
  var p=svgPt(ev);G.drag={id:ev.pointerId,last:p};G.refs.hover.setAttribute('d','');clickAt(p);
});
svg.addEventListener('pointermove',function(ev){
  var p=svgPt(ev);
  if(G.drag&&G.drag.id===ev.pointerId){ev.preventDefault();dragTo(p);}
  else if(ev.pointerType==='mouse'&&!G.drag)hoverAt(p);
});
function endDrag(ev){if(G.drag&&G.drag.id===ev.pointerId)G.drag=null;}
svg.addEventListener('pointerup',endDrag);svg.addEventListener('pointercancel',endDrag);
svg.addEventListener('pointerleave',function(ev){if(ev.pointerType==='mouse'&&G.refs)G.refs.hover.setAttribute('d','');});
svg.addEventListener('touchmove',function(e){e.preventDefault();},{passive:false});

/* =====================================================================
   SUBMIT, REVEAL, RESULT
   ===================================================================== */
function gaugeHTML(){
  var t='';for(var k=0;k<=4;k++){var a=Math.PI-k*Math.PI/4,c=Math.cos(a),s=Math.sin(a);t+='<line class="g-tick" x1="'+(80+c*68).toFixed(1)+'" y1="'+(82-s*68).toFixed(1)+'" x2="'+(80+c*74).toFixed(1)+'" y2="'+(82-s*74).toFixed(1)+'"/>';}
  return '<svg class="gauge-svg" viewBox="0 0 160 126" aria-hidden="true"><path class="g-track" d="M20 82A60 60 0 0 1 140 82" pathLength="100"/><path class="g-val" d="M20 82A60 60 0 0 1 140 82" pathLength="100"/>'+t+
    '<g class="g-needle"><line x1="80" y1="82" x2="80" y2="38"/><circle cx="80" cy="82" r="5"/></g><text class="g-pct" x="80" y="110">0%</text><text class="g-cap" x="80" y="123">EFFICIENCY</text></svg>';
}
function setGauge(root,pct,animate,label){
  var val=root.querySelector('.g-val'),nd=root.querySelector('.g-needle'),tx=root.querySelector('.g-pct');
  var col=pct>=90?'var(--start)':pct>=60?'var(--optimal)':'var(--end)';
  val.style.stroke=col;
  var apply=function(){val.style.strokeDasharray=pct+' 100';nd.style.transform='rotate('+(-90+pct*1.8)+'deg)';};
  if(animate&&!reduceMotion()){requestAnimationFrame(function(){requestAnimationFrame(apply);});}else apply();
  tx.textContent=label!==undefined?label:pct.toFixed(1)+'%';
}
function countTo(el,final,fmt,ms,tok){
  if(reduceMotion()||ms<=0){el.textContent=fmt(final);return;}
  tween(ms,function(p){el.textContent=fmt(final*ease(p));},tok).then(function(ok){if(ok)el.textContent=fmt(final);});
}
function recordResult(res){
  var c=G.city;
  if(G.mode==='daily'){S.daily[G.dateKey]={seed:G.seed,diff:G.diff,path:G.route.slice(),dist:res.dist,opt:res.opt,eff:res.eff,points:res.points,turns:res.turns};save();}
  else if(G.counted){var p=S.practice;p.completed++;p.totalEff+=res.eff;p.totalPoints+=res.points;p.bestEff=Math.max(p.bestEff,res.eff);p.bestScore=Math.max(p.bestScore,res.points);if(res.exact>=0.9999)p.perfect++;p.byDiff[G.diff]++;save();}
}
function submitRoute(){
  if(G.locked)return;
  var v=validateRoute(G.city,G.route);
  if(!v.ok){toast(v.msg,'error');Sound.play('error');return;}
  lockRoute(true);
}
function lockRoute(fresh){
  G.locked=true;G.drag=null;
  var res=scoreRoute(G.city,G.route);G.result=res;
  if(fresh)recordResult(res);
  G.refs.hover.setAttribute('d','');svg.classList.add('locked');
  refresh(false);$('controlsWrap').hidden=true;
  if(fresh){
    Sound.play('submit');
    /* With motion reduced there is no reveal animation to time the reward to, so follow the confirmation directly. */
    if(res.exact>=0.9999&&reduceMotion())setTimeout(function(){if(G.locked&&G.result===res)Sound.play('optimal');},330);
  }
  runReveal(fresh&&!reduceMotion());
}
async function runReveal(animate){
  var tok=++G.anim,res=G.result,c=G.city,r=G.refs,N=c.nodes,box=$('result');
  var od=pathD(c.optimal.path);
  r.opt.setAttribute('d',od);r.optGlow.setAttribute('d',od);
  [r.opt,r.optGlow].forEach(function(p){p.style.strokeDasharray='1000';p.style.strokeDashoffset=animate?'1000':'0';});
  r.car.style.display='none';
  box.hidden=false;box.dataset.stage='1';
  $('resEyebrow').textContent=G.review?'Completed':'Route locked';
  $('resLabel').textContent=animate?'Locked in':res.label;
  $('rlDist').textContent=fmtM(res.dist);$('rlTurns').textContent=res.turns;
  $('gaugeBox').innerHTML=gaugeHTML();
  $('retryBtn').hidden=G.mode==='daily';$('replayBtn').disabled=true;
  var notes=[];
  if(G.mode==='daily')notes.push(G.review?'Daily challenge completed. A fresh city arrives tomorrow.':'Daily result saved on this device. A fresh city arrives tomorrow.');
  else if(!G.counted)notes.push('Practice retry. This attempt is not counted in your statistics.');
  else notes.push('Practice result saved.');
  if(!storageOK)notes.push('Storage is unavailable, so progress lasts only until you close this page.');
  $('resNote').textContent=notes.join(' ');
  $('nextBtn').textContent=G.mode==='daily'?'Try practice mode':'Next challenge';
  var finish=function(count){
    box.dataset.stage='2';$('resEyebrow').textContent=G.review?'Completed':'Result';$('resLabel').textContent=res.label;
    $('replayBtn').disabled=false;
    var ms=count?900:0;
    countTo($('tDist'),res.dist,fmtM,ms,tok);countTo($('tOpt'),res.opt,fmtM,ms,tok);countTo($('tExtra'),res.extra,fmtM,ms,tok);
    countTo($('tEff'),res.eff,function(v){return v.toFixed(1)+'%';},ms,tok);
    countTo($('tPts'),res.points,function(v){return Math.round(v).toLocaleString('en-GB');},ms,tok);
    $('tTurns').textContent=res.turns;
    setGauge($('gaugeBox'),res.eff,count,res.eff.toFixed(1)+'%');
    if(count&&res.exact>=0.9999)Sound.play('optimal'); /* reveal finished on an optimal route */
  };
  if(!animate){[r.opt,r.optGlow].forEach(function(p){p.style.strokeDashoffset='0';});finish(false);return;}
  if(!await sleep(950,tok))return;
  var len=r.opt.getTotalLength(),m=parseFloat(r.car.dataset.m||'1');
  r.car.style.display='';
  var ok=await tween(Math.min(3200,Math.max(1700,len*2.2)),function(p){
    var e=ease(p),l=e*len,a=r.opt.getPointAtLength(l),b=r.opt.getPointAtLength(Math.min(len,l+2));
    var off=1000*(1-e);r.opt.style.strokeDashoffset=off;r.optGlow.style.strokeDashoffset=off;
    r.car.setAttribute('transform','translate('+a.x.toFixed(1)+' '+a.y.toFixed(1)+') rotate('+(Math.atan2(b.y-a.y,b.x-a.x)*180/Math.PI).toFixed(1)+') scale('+(1.15*m).toFixed(2)+')');
  },tok);
  if(!ok)return;
  r.car.style.display='none';
  finish(true);
  box.scrollIntoView({behavior:reduceMotion()?'auto':'smooth',block:'nearest'});
}
function shareText(){
  var r=G.result,label=G.mode==='daily'?'Daily '+G.dateKey:'Practice';
  return 'THE WRONG WAY · '+label+' · '+DIFF_LABEL[G.diff].toUpperCase()+'\n'+r.eff.toFixed(1)+'% efficiency · '+r.points+' pts\n'+fmtM(r.dist)+' driven vs '+fmtM(r.opt)+' optimal';
}
async function copyText(t){
  try{await navigator.clipboard.writeText(t);return true;}catch(e){}
  try{var ta=document.createElement('textarea');ta.value=t;ta.style.position='fixed';ta.style.opacity='0';document.body.appendChild(ta);ta.select();var ok=document.execCommand('copy');ta.remove();return ok;}catch(e2){return false;}
}

/* =====================================================================
   GAME SETUP
   ===================================================================== */
function startGame(mode,opts){
  opts=opts||{};G.mode=mode;
  if(mode==='daily'){G.dateKey=dateKey();G.diff=dailyDifficulty(G.dateKey);G.seed=hashString('wrongway:'+G.dateKey+':'+G.diff);}
  else{G.dateKey='';G.diff=opts.diff||S.settings.practiceDiff;G.seed=(Date.now()^Math.floor(Math.random()*4294967296))>>>0;}
  G.city=generateCity(G.seed,G.diff);setupBoard();
}
function setupBoard(){
  var c=G.city;G.anim++;
  buildMapSVG(svg,c,{buildings:S.settings.buildings});grabRefs();
  G.route=[c.start];G.locked=false;G.result=null;G.review=false;G.counted=true;
  svg.classList.remove('locked');$('result').hidden=true;$('controlsWrap').hidden=false;
  var isDaily=G.mode==='daily';
  $('gMode').textContent=isDaily?'Daily challenge':'Practice mode';
  $('gTitle').textContent=isDaily?prettyDate()+' · '+DIFF_LABEL[G.diff]:'Map #'+(G.seed%100000).toString().padStart(5,'0')+' · '+DIFF_LABEL[G.diff];
  $('diffSeg').hidden=isDaily;$('newMapBtn').hidden=isDaily;
  syncDiffSeg();
  var badge=$('gBadge');badge.className='badge';badge.textContent='';
  if(isDaily){badge.textContent='One map per day';}
  else badge.textContent='Unlimited attempts';
  if(G.view==='game'||true){G.u=applyScale(svg);}
  var mf=$('mapFrame');mf.classList.remove('enter');void mf.offsetWidth;if(!reduceMotion())mf.classList.add('enter');
  refresh(false);
  var rec=isDaily?S.daily[G.dateKey]:null;
  if(rec&&validateRoute(c,rec.path).ok){
    G.route=rec.path.slice();G.review=true;badge.textContent='Completed today';badge.classList.add('ok');
    lockRoute(false);
  }else{
    toast('Click a ringed junction or drag along the streets from A to B.','info');
  }
}
function syncDiffSeg(){var b=$('diffSeg').querySelectorAll('button');for(var i=0;i<b.length;i++)b[i].setAttribute('aria-pressed',String(b[i].dataset.diff===G.diff));}
async function retryMap(){
  G.counted=false;G.anim++;G.route=[G.city.start];G.locked=false;G.result=null;G.review=false;
  svg.classList.remove('locked');$('result').hidden=true;$('controlsWrap').hidden=false;
  G.refs.opt.setAttribute('d','');G.refs.optGlow.setAttribute('d','');G.refs.car.style.display='none';
  var badge=$('gBadge');badge.className='badge warn';badge.textContent='Retry · not counted';
  refresh(false);window.scrollTo({top:0,behavior:reduceMotion()?'auto':'smooth'});
}
function nextChallenge(){
  if(G.mode==='daily'){navigate('practice',{fresh:true});}
  else{startGame('practice',{diff:G.diff});window.scrollTo({top:0,behavior:reduceMotion()?'auto':'smooth'});}
}

/* =====================================================================
   STATISTICS
   ===================================================================== */
function computeStreak(){
  var k=S.daily,d=new Date();d.setHours(12,0,0,0);
  if(!k[dateKey(d)])d.setDate(d.getDate()-1);
  var n=0;while(k[dateKey(d)]){n++;d.setDate(d.getDate()-1);}return n;
}
function longestStreak(){
  var keys=Object.keys(S.daily).sort(),best=0,run=0,prev=null;
  keys.forEach(function(k){var p=k.split('-').map(Number),d=new Date(p[0],p[1]-1,p[2],12);
    if(prev){var n=new Date(prev);n.setDate(n.getDate()+1);run=dateKey(n)===k?run+1:1;}else run=1;
    prev=d;best=Math.max(best,run);});
  return best;
}
function aggregate(){
  var ds=Object.keys(S.daily).map(function(k){return S.daily[k];}),pr=S.practice;
  var dCount=ds.length,pCount=pr.completed;
  var bestEff=Math.max(pr.bestEff,ds.reduce(function(m,r){return Math.max(m,r.eff);},0));
  var bestScore=Math.max(pr.bestScore,ds.reduce(function(m,r){return Math.max(m,r.points);},0));
  var dEff=dCount?ds.reduce(function(s,r){return s+r.eff;},0)/dCount:0,pEff=pCount?pr.totalEff/pCount:0;
  var perfect=pr.perfect+ds.filter(function(r){return r.eff>=99.95;}).length;
  var dPts=ds.reduce(function(s,r){return s+r.points;},0);
  return {dCount:dCount,pCount:pCount,total:dCount+pCount,bestEff:bestEff,bestScore:bestScore,dEff:dEff,pEff:pEff,perfect:perfect,totalPts:dPts+pr.totalPoints,streak:computeStreak(),longest:longestStreak()};
}
function effClass(v){return v>=90?'g':v>=60?'y':'r';}
function barRow(label,valText,pct,cls){
  var row=document.createElement('div');row.className='bar-row';
  var top=document.createElement('div');top.className='top';var a=document.createElement('span');a.textContent=label;var b=document.createElement('span');b.textContent=valText;top.append(a,b);
  var bar=document.createElement('div');bar.className='bar';var i=document.createElement('i');if(cls)i.className=cls;bar.appendChild(i);row.append(top,bar);
  requestAnimationFrame(function(){requestAnimationFrame(function(){i.style.width=clamp(pct,0,100)+'%';});});
  return row;
}
function kpi(label,value,small){
  var c=document.createElement('div');c.className='card kpi';var e=document.createElement('div');e.className='eyebrow';e.textContent=label;
  var v=document.createElement('div');v.className='v';v.textContent=value;if(small){var s=document.createElement('small');s.textContent=' '+small;v.appendChild(s);}c.append(e,v);return c;
}
function renderStats(){
  var body=$('statsBody');body.textContent='';var A=aggregate();
  if(A.total===0){
    var em=document.createElement('div');em.className='empty';var b=document.createElement('b');b.textContent='No routes driven yet';em.append(b,'Finish a daily or practice challenge and your record will show up here.');
    var go=document.createElement('button');go.className='btn primary';go.style.marginTop='14px';go.textContent='Start driving';go.addEventListener('click',function(){navigate(S.daily[dateKey()]?'practice':'daily');});em.append(document.createElement('br'),go);body.appendChild(em);
  }
  var g=document.createElement('div');g.className='grid4';
  g.append(kpi('Challenges completed',String(A.total)),kpi('Best score',A.bestScore.toLocaleString('en-GB'),'/ 1,000'),kpi('Best efficiency',A.bestEff?A.bestEff.toFixed(1)+'%':'—'),kpi('Daily streak',String(A.streak),A.streak===1?'day':'days'));
  body.appendChild(g);
  var g2=document.createElement('div');g2.className='grid2';
  var c1=document.createElement('div');c1.className='card';var h1=document.createElement('div');h1.className='eyebrow';h1.textContent='Efficiency & scoring';c1.appendChild(h1);
  c1.append(barRow('Average efficiency · daily',A.dCount?A.dEff.toFixed(1)+'%':'—',A.dEff,effClass(A.dEff)),
    barRow('Average efficiency · practice',A.pCount?A.pEff.toFixed(1)+'%':'—',A.pEff,effClass(A.pEff)),
    barRow('Best score',A.bestScore+' / 1000',A.bestScore/10,'y'),
    barRow('Perfect routes',A.perfect+' of '+A.total,A.total?A.perfect/A.total*100:0,'g'));
  var c2=document.createElement('div');c2.className='card';var h2=document.createElement('div');h2.className='eyebrow';h2.textContent='Practice by difficulty';c2.appendChild(h2);
  var mx=Math.max(1,S.practice.byDiff.easy,S.practice.byDiff.medium,S.practice.byDiff.hard);
  ['easy','medium','hard'].forEach(function(k){c2.appendChild(barRow(DIFF_LABEL[k],String(S.practice.byDiff[k]),S.practice.byDiff[k]/mx*100));});
  var h3=document.createElement('div');h3.className='eyebrow';h3.style.marginTop='20px';h3.textContent='Last 7 days';c2.appendChild(h3);
  var wk=document.createElement('div');wk.className='week';
  var d=new Date();d.setHours(12,0,0,0);d.setDate(d.getDate()-6);
  for(var i=0;i<7;i++){var k=dateKey(d),r=S.daily[k],cell=document.createElement('div');if(r)cell.className='hit';
    cell.textContent=d.toLocaleDateString('en-GB',{weekday:'short'}).toUpperCase();var bb=document.createElement('b');bb.textContent=r?Math.round(r.eff)+'%':'·';cell.appendChild(bb);wk.appendChild(cell);d.setDate(d.getDate()+1);}
  c2.appendChild(wk);
  g2.append(c1,c2);body.appendChild(g2);
  var g3=document.createElement('div');g3.className='grid4';g3.style.marginTop='12px';
  g3.append(kpi('Daily completed',String(A.dCount)),kpi('Practice completed',String(A.pCount)),kpi('Longest streak',String(A.longest),A.longest===1?'day':'days'),kpi('Total points',A.totalPts.toLocaleString('en-GB')));
  body.appendChild(g3);
}
function renderHome(){
  var A=aggregate();
  $('hsBest').textContent=A.bestEff?A.bestEff.toFixed(1)+'%':'—';$('hsDone').textContent=A.total;
  $('hsStreak').innerHTML='';$('hsStreak').append(String(A.streak));var sm=document.createElement('small');sm.textContent=A.streak===1?' day':' days';$('hsStreak').appendChild(sm);
  var gb=$('homeGauge');if(!gb.firstChild)gb.innerHTML=gaugeHTML();
  setGauge(gb,A.bestEff||0,false,A.bestEff?Math.round(A.bestEff)+'%':'—');
  var key=dateKey(),rec=S.daily[key],chip=$('dailyChip');
  chip.classList.toggle('done',!!rec);
  $('dailyChipText').textContent=prettyDate()+' · Daily · '+DIFF_LABEL[dailyDifficulty(key)]+(rec?' · Completed '+rec.eff.toFixed(1)+'%':' · Not played yet');
  $('startBtn').lastChild.textContent=rec?'Start driving':'Start driving';
}
function paintVol(){var r=$('volRange');r.style.setProperty('--p',r.value+'%');$('volOut').textContent=r.value+'%';r.setAttribute('aria-valuetext',r.value+' percent');}
function renderSettings(){
  var s=S.settings;
  [['themeSeg','theme','theme'],['setDiffSeg','diff','practiceDiff'],['motionSeg','motion','motion']].forEach(function(t){
    var bs=$(t[0]).querySelectorAll('button');for(var i=0;i<bs.length;i++)bs[i].setAttribute('aria-pressed',String(bs[i].dataset[t[1]]===s[t[2]]));});
  $('swHints').setAttribute('aria-checked',String(s.hints));$('swBuild').setAttribute('aria-checked',String(s.buildings));
  $('swSound').setAttribute('aria-checked',String(s.sound&&Sound.supported));$('swSound').disabled=!Sound.supported;
  $('volRange').value=Math.round(s.volume*100);$('volRange').disabled=!(s.sound&&Sound.supported);paintVol();
  $('soundDesc').textContent=Sound.supported?'Short, quiet cues for drawing, undoing and submitting. Off until you turn it on.':'This browser has no Web Audio support, so sound is unavailable. The game plays the same without it.';
  $('storageNote').textContent=storageOK?'Progress is stored locally in this browser only.':'Local storage is unavailable. Your progress will last only until you close this page.';
}

/* =====================================================================
   NAVIGATION, DRAWER, MODAL
   ===================================================================== */
var PILL={home:'Home',daily:'Daily challenge',practice:'Practice',stats:'Statistics',settings:'Settings',about:'About'};
function showView(name){
  document.querySelectorAll('.view').forEach(function(v){v.hidden=v.id!=='view-'+name;});
  G.view=name;
}
function navigate(nav,opts){
  opts=opts||{};closeDrawer(true);
  if(nav==='daily'){if(!(G.mode==='daily'&&G.city&&G.dateKey===dateKey()))startGame('daily');showView('game');}
  else if(nav==='practice'){if(opts.fresh||!(G.mode==='practice'&&G.city))startGame('practice');showView('game');}
  else{showView(nav);if(nav==='stats')renderStats();if(nav==='home')renderHome();if(nav==='settings')renderSettings();}
  G.nav=nav;$('modePill').textContent=PILL[nav]||'';
  document.querySelectorAll('.nav-item').forEach(function(b){if(b.dataset.nav===nav)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current');});
  try{history.replaceState(null,'','#'+nav);}catch(e){}
  if(nav==='daily'||nav==='practice'){G.u=applyScale(svg);if(G.refs)refresh(false);}
  window.scrollTo(0,0);
}
var lastFocus=null;
function openDrawer(){
  lastFocus=document.activeElement;$('drawer').classList.add('open');$('drawer').setAttribute('aria-hidden','false');$('backdrop').classList.add('show');$('menuBtn').setAttribute('aria-expanded','true');
  ['topbar','main'].forEach(function(i){$(i).inert=true;});document.querySelector('.foot').inert=true;
  setTimeout(function(){$('closeBtn').focus();},30);
}
function closeDrawer(skipFocus){
  if(!$('drawer').classList.contains('open'))return;
  $('drawer').classList.remove('open');$('drawer').setAttribute('aria-hidden','true');$('backdrop').classList.remove('show');$('menuBtn').setAttribute('aria-expanded','false');
  ['topbar','main'].forEach(function(i){$(i).inert=false;});document.querySelector('.foot').inert=false;
  if(!skipFocus)$('menuBtn').focus();
}
var modalResolve=null,modalFocus=null;
function confirmBox(title,text,okLabel){
  return new Promise(function(res){
    modalResolve=res;modalFocus=document.activeElement;
    $('mTitle').textContent=title;$('mText').textContent=text;$('mOk').textContent=okLabel||'Confirm';$('modal').hidden=false;$('mCancel').focus();Sound.play('modal');
  });
}
function closeModal(v){if($('modal').hidden)return;$('modal').hidden=true;var r=modalResolve;modalResolve=null;if(modalFocus&&modalFocus.focus)try{modalFocus.focus();}catch(e){}if(r)r(v);}

/* =====================================================================
   EVENT WIRING
   ===================================================================== */
document.querySelectorAll('[data-nav]').forEach(function(el){el.addEventListener('click',function(e){e.preventDefault();navigate(el.dataset.nav);});});
$('menuBtn').addEventListener('click',openDrawer);$('closeBtn').addEventListener('click',function(){closeDrawer();});$('backdrop').addEventListener('click',function(){closeDrawer();});
$('settingsBtn').addEventListener('click',function(){navigate('settings');});
$('mOk').addEventListener('click',function(){closeModal(true);});$('mCancel').addEventListener('click',function(){closeModal(false);});
$('modal').addEventListener('pointerdown',function(e){if(e.target===$('modal'))closeModal(false);});
document.addEventListener('keydown',function(e){
  if(e.key==='Escape'){if(!$('modal').hidden){closeModal(false);return;}closeDrawer();return;}
  if((e.ctrlKey||e.metaKey)&&!e.shiftKey&&e.key.toLowerCase()==='z'&&G.view==='game'&&$('modal').hidden&&!$('drawer').classList.contains('open')){
    var t=e.target&&e.target.tagName;if(t==='INPUT'||t==='TEXTAREA')return;e.preventDefault();undo();}
  if(e.key==='Tab'&&!$('modal').hidden){var els=$('modal').querySelectorAll('button'),first=els[0],last=els[els.length-1];
    if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}}
});
$('startBtn').addEventListener('click',function(){navigate(S.daily[dateKey()]?'practice':'daily',{fresh:!S.daily[dateKey()]?false:true});});
$('practiceBtn').addEventListener('click',function(){navigate('practice',{fresh:true});});
$('undoBtn').addEventListener('click',undo);$('clearBtn').addEventListener('click',clearRoute);$('resetBtn').addEventListener('click',resetBoard);$('submitBtn').addEventListener('click',submitRoute);
$('replayBtn').addEventListener('click',function(){if(G.locked)runReveal(!reduceMotion());});
$('retryBtn').addEventListener('click',retryMap);$('nextBtn').addEventListener('click',nextChallenge);
$('shareBtn').addEventListener('click',async function(){var ok=await copyText(shareText());toast(ok?'Result copied to clipboard.':'Could not copy. Select the numbers manually.',ok?'good':'error');Sound.play(ok?'confirm':'error');
  var b=$('shareBtn');if(ok){b.textContent='Copied!';setTimeout(function(){b.textContent='Copy result';},1600);}});
$('newMapBtn').addEventListener('click',function(){startGame('practice',{diff:G.diff});});
$('diffSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;
  if(b.dataset.diff===G.diff&&G.route.length<=1&&!G.locked)return;
  S.settings.practiceDiff=b.dataset.diff;save();startGame('practice',{diff:b.dataset.diff});});
$('themeSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;S.settings.theme=b.dataset.theme;save();applyTheme();renderSettings();});
$('setDiffSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;S.settings.practiceDiff=b.dataset.diff;save();renderSettings();});
$('motionSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;S.settings.motion=b.dataset.motion;save();applyMotion();renderSettings();});
/* buttons that play their own, more specific sound opt out of the generic interface tick */
['undoBtn','clearBtn','resetBtn','submitBtn','shareBtn','mOk','wipeBtn'].forEach(function(id){$(id).dataset.snd='none';});
$('swSound').addEventListener('click',function(){
  S.settings.sound=!S.settings.sound;save();renderSettings();
  if(S.settings.sound){Sound.unlock().then(function(ok){if(ok){Sound.setVolume();Sound.play('on');}});}
  else{Sound.play('off',{force:true});setTimeout(Sound.sync,400);} /* confirm blip, then release the audio device */
});
$('volRange').addEventListener('input',function(){
  S.settings.volume=Math.round(clamp(Number(this.value)/100,0,1)*100)/100;paintVol();Sound.setVolume();
});
$('volRange').addEventListener('change',function(){save();Sound.play('tap');}); /* audible sample at the new level */
$('swHints').addEventListener('click',function(){S.settings.hints=!S.settings.hints;save();renderSettings();if(G.refs)refresh(false);});
$('swBuild').addEventListener('click',function(){S.settings.buildings=!S.settings.buildings;save();renderSettings();
  if(G.city){var keep=G.route.slice(),lk=G.locked,rv=G.review;buildMapSVG(svg,G.city,{buildings:S.settings.buildings});grabRefs();G.u=applyScale(svg);G.route=keep;
    if(lk&&G.result){svg.classList.add('locked');var od=pathD(G.city.optimal.path);G.refs.opt.setAttribute('d',od);G.refs.optGlow.setAttribute('d',od);
      [G.refs.opt,G.refs.optGlow].forEach(function(p){p.style.strokeDasharray='1000';p.style.strokeDashoffset=$('result').dataset.stage==='2'?'0':'1000';});}
    else svg.classList.remove('locked');refresh(false);}});
$('wipeBtn').addEventListener('click',async function(){
  var ok=await confirmBox('Reset all data?','This permanently deletes every daily result, practice statistic, streak and setting stored in this browser.','Delete everything');
  if(!ok)return;
  Sound.play('clear');
  S=defaults();save();applyTheme();applyMotion();Sound.sync();renderSettings();G.city=null;G.mode='daily';G.refs=null;toast('All data reset.','info');
});

var rsT=0;
function onResize(){clearTimeout(rsT);rsT=setTimeout(function(){
  if(G.city&&G.refs&&G.view==='game'){G.u=applyScale(svg);refresh(false);}
  var pv=$('previewSvg');if(pv.firstChild&&G.view==='home')applyScale(pv);
},60);}
if(window.ResizeObserver){new ResizeObserver(onResize).observe($('mapFrame'));new ResizeObserver(onResize).observe(document.querySelector('.preview'));}
window.addEventListener('resize',onResize);
if(window.matchMedia){try{matchMedia('(prefers-reduced-motion: reduce)').addEventListener('change',applyMotion);}catch(e){}}

/* =====================================================================
   BOOT
   ===================================================================== */
function renderPreview(){
  var pv=$('previewSvg'),city=generateCity((Date.now()^0x5bd1e995)>>>0,'medium');
  buildMapSVG(pv,city,{buildings:true});
  var od=pathD2(city,city.optimal.path),o=pv.querySelector('.opt'),og=pv.querySelector('.opt-glow');
  o.setAttribute('d',od);og.setAttribute('d',od);o.classList.add('preview-anim');og.classList.add('preview-anim');
  applyScale(pv);
}
function pathD2(city,ids){return 'M'+ids.map(function(i){return f(city.nodes[i].x)+' '+f(city.nodes[i].y);}).join('L');}
applyTheme();applyMotion();
(function boot(){
  try{renderPreview();}catch(e){}
  var h=(location.hash||'').replace('#','');
  navigate(PILL[h]?h:'home');
})();
})();
});
