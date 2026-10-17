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

/* Road rules. An edge may carry e.closed ('works' | 'crash') or e.ow (the node id travel is allowed FROM).
   Classic (v1) edges carry neither, so every classic city behaves exactly as before.
   canGo() is the single source of truth: drawing, validation, Dijkstra, hints and traffic all use it. */
function canGo(e,from){return !e.closed&&(e.ow==null||e.ow===from);}
function dijkstra(city,src,wm){ /* wm (optional): per-edge weight multipliers, used only to model an imperfect planner */
  var n=city.nodes.length,dist=new Array(n).fill(Infinity),prev=new Array(n).fill(-1),hops=new Array(n).fill(0);
  dist[src]=0;var h=new MinHeap();h.push(0,src);
  while(h.a.length){var top=h.pop(),d=top[0],u=top[1];if(d>dist[u])continue;
    var nb=city.adj[u];for(var k=0;k<nb.length;k++){var ed=nb[k].e;if(!canGo(ed,u))continue;var to=nb[k].to,nd=d+(wm?ed.w*wm[ed.id]:ed.w);if(nd<dist[to]){dist[to]=nd;prev[to]=u;hops[to]=hops[u]+1;h.push(nd,to);}}}
  return {dist:dist,prev:prev,hops:hops};
}
/* Distance-to-destination for every junction, following the same legal directions (reverse search). */
function dijkstraTo(city,dst){
  var n=city.nodes.length,dist=new Array(n).fill(Infinity);
  dist[dst]=0;var h=new MinHeap();h.push(0,dst);
  while(h.a.length){var top=h.pop(),d=top[0],u=top[1];if(d>dist[u])continue;
    var nb=city.adj[u];for(var k=0;k<nb.length;k++){var ed=nb[k].e,v=nb[k].to;if(!canGo(ed,v))continue;var nd=d+ed.w;if(nd<dist[v]){dist[v]=nd;h.push(nd,v);}}}
  return dist;
}
function pathTo(prev,src,dst){var p=[],c=dst;while(c!==-1){p.push(c);if(c===src)break;c=prev[c];}p.reverse();return p[0]===src?p:null;}
function edgeBetween(city,a,b){return city.emap.get(edgeKey(a,b))||null;}

/* X is undefined for every classic (v1) map, including ALL Daily maps. That path is byte-for-byte the original generator:
   same RNG, same call order, same parameters. X only exists for the strategic (v2) generator used by Practice and Journey;
   it adds a river and extra stubs using a second, independent RNG (rng2) and leaves start/finish selection to the caller. */
function tryGenerate(seed,diff,X){
  var P=DIFF[diff],rng=mulberry32(seed>>>0);
  var rng2=null,riverInfo=null;
  if(X){if(X.p)P=Object.assign({},P,X.p);rng2=mulberry32((seed^0xA5F1C3D7)>>>0);}
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
  // strategic maps only: a river between two grid columns, crossable only at a few bridges
  if(X&&X.river){
    var lo=Math.floor(cols*.34),hi=Math.floor(cols*.62),c0=lo+Math.floor(rng2()*(hi-lo+1));
    var cross=[];
    emap.forEach(function(e){if((nodes[e.a].gi<=c0)!==(nodes[e.b].gi<=c0))cross.push(e);});
    var midY=function(e){return (nodes[e.a].y+nodes[e.b].y)/2;};
    cross.sort(function(p,q){return midY(p)-midY(q)||p.a-q.a;});
    var order=cross.map(function(_,ix){return ix;}),keep=[],minGap=(H-2*my)*.21;
    for(i=order.length-1;i>0;i--){var r3=Math.floor(rng2()*(i+1)),t3=order[i];order[i]=order[r3];order[r3]=t3;}
    for(i=0;i<order.length&&keep.length<X.river;i++){var ce=cross[order[i]],okb=true;
      for(j=0;j<keep.length;j++)if(Math.abs(midY(keep[j])-midY(ce))<minGap)okb=false;
      if(okb)keep.push(ce);}
    if(keep.length<Math.min(2,X.river))return null;
    cross.forEach(function(e){if(keep.indexOf(e)<0)delEdge(e);});
    if(!connected())return null;
    keep.forEach(function(e){e.bridge=true;});
    var rp=[];
    for(j=0;j<rows;j++){var qa=nodes[j*cols+c0],qb=nodes[j*cols+c0+1];rp.push({x:(qa.x+qb.x)/2,y:(qa.y+qb.y)/2});}
    rp.unshift({x:rp[0].x,y:-30});rp.push({x:rp[rp.length-1].x,y:H+30});
    riverInfo={pts:rp,w:Math.round((W-2*mx)/(cols-1)*.4),c:c0};
    for(j=0;j<rows-1;j++)used.add(j*cols+c0);   // no cul-de-sacs on the river banks
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
  if(riverInfo){ // which bank each junction is on (stubs inherit from the junction they hang off)
    nodes.forEach(function(q){q.sd=q.stub?-1:(q.gi<=riverInfo.c?0:1);});
    nodes.forEach(function(q){if(q.stub)nbr[q.id].forEach(function(o){q.sd=nodes[o].sd;});});
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
  if(X){ /* strategic map: the caller picks start/finish and applies road rules */
    city.gen=2;if(riverInfo)city.river=riverInfo;
    edges.forEach(function(ed,ix){if(el[ix].bridge)ed.bridge=true;});
    return city;
  }
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

/* =====================================================================
   STRATEGIC GENERATOR (v2) — Practice and Journey only. Daily never calls this.
   Idea: build a classic-style network (plus an optional river with a few bridges), then CHOOSE the start/finish pair
   whose route is genuinely tricky, using measurable properties of the pair, then optionally add road rules.
   Every random choice comes from seeded RNGs, so the same seed always gives the same map.
   The pair selection below uses only + - * / sqrt and comparisons, so it cannot differ between browsers. The network itself is built by the same code as Daily maps.
   ===================================================================== */
function sqd(a,b){var dx=a.x-b.x,dy=a.y-b.y;return Math.sqrt(dx*dx+dy*dy);}
function bfsPrev(city,src){
  var n=city.nodes.length,prev=new Array(n).fill(-1),seen=new Uint8Array(n),q=[src],qi=0;seen[src]=1;
  while(qi<q.length){var u=q[qi++],nb=city.adj[u];for(var k=0;k<nb.length;k++){if(!canGo(nb[k].e,u))continue;var v=nb[k].to;if(!seen[v]){seen[v]=1;prev[v]=u;q.push(v);}}}
  return prev;
}
function pathCost(city,path){var d=0;for(var i=1;i<path.length;i++)d+=edgeBetween(city,path[i-1],path[i]).w;return d;}
/* Always step to the neighbour that looks closest to B ("the visually direct way"). -1 if it gets stuck. */
function greedyCost(city,s,e){
  var N=city.nodes,cur=s,seen={},cost=0,steps=0;seen[s]=1;
  while(cur!==e&&steps++<400){
    var best=-1,bd=Infinity,bw=0,nb=city.adj[cur];
    for(var k=0;k<nb.length;k++){var to=nb[k].to;if(seen[to]||!canGo(nb[k].e,cur))continue;var d=sqd(N[to],N[e]);if(d<bd){bd=d;best=to;bw=nb[k].e.w;}}
    if(best<0)return -1;
    seen[best]=1;cost+=bw;cur=best;
  }
  return cur===e?cost:-1;
}
/* How well does a "sensible but unplanned" driver do? Biased random walks that lean towards B.
   High ease means a perfect score is cheap; low ease means planning pays off. */
function walkEase(city,s,e,opt,rng,tries){
  var N=city.nodes,sum=0,ok=0,k;
  for(var t=0;t<tries;t++){
    var cur=s,seen={},cost=0,steps=0;seen[s]=1;
    while(cur!==e&&steps++<300){
      var nb=city.adj[cur],opts=[],dmin=Infinity,tot=0;
      for(k=0;k<nb.length;k++){var to=nb[k].to;if(seen[to]||!canGo(nb[k].e,cur))continue;var d=sqd(N[to],N[e]);opts.push([to,nb[k].e.w,d]);if(d<dmin)dmin=d;}
      if(!opts.length){cur=-1;break;}
      var ws=opts.map(function(o){var q=(o[2]-dmin)/36,w=1/(1+q*q);tot+=w;return w;}),r=rng()*tot,pick=opts.length-1;
      for(k=0;k<ws.length;k++){r-=ws[k];if(r<=0){pick=k;break;}}
      seen[opts[pick][0]]=1;cost+=opts[pick][1];cur=opts[pick][0];
    }
    if(cur===e){sum+=opt/cost;ok++;}
  }
  return ok?sum/ok:.6;
}
/* Distinct alternative routes found by blocking single roads along the best route; returns their cost ratios. */
function altRatios(city,s,e,path,opt){
  var out=[],sigs={},L=path.length-1,tried={};
  for(var t=0;t<6&&L>2;t++){
    var i=1+Math.floor((L-1)*(t+.5)/6);if(tried[i]||i<1||i>L)continue;tried[i]=1;
    var ep=edgeBetween(city,path[i-1],path[i]);if(!ep||ep.closed)continue;
    ep.closed='tmp';var D2;try{D2=dijkstra(city,s);}finally{delete ep.closed;}
    if(isFinite(D2.dist[e])){var p2=pathTo(D2.prev,s,e),sg=p2.join(',');if(!sigs[sg]){sigs[sg]=1;out.push(D2.dist[e]/opt);}}
  }
  return out;
}
/* An imperfect planner: finds the shortest route while misjudging every road's length by up to ±22%.
   If even this driver usually lands on the optimum, the map is easy; if it often doesn't, planning matters. */
function noisyEff(city,s,e,opt,rng,tries){
  var sum=0,wm=new Array(city.edges.length);
  for(var t=0;t<tries;t++){
    for(var i=0;i<wm.length;i++)wm[i]=.78+rng()*.44;
    var D=dijkstra(city,s,wm),p=pathTo(D.prev,s,e);
    sum+=p?opt/pathCost(city,p):.5;
  }
  return sum/tries;
}
var PICK_PCT=[0,.5,.85,.95]; /* which rank of the candidate pairs (0 = easiest, 1 = hardest) each tier picks */
function pairMetrics(city,s,e,D,bp,rng){
  var opt=D.dist[e],path=pathTo(D.prev,s,e),hp=pathTo(bp,s,e);
  var hopEx=hp?pathCost(city,hp)/opt-1:0,gc=greedyCost(city,s,e),gEx=gc<0?.3:gc/opt-1;
  var ease=walkEase(city,s,e,opt,rng,16),noisy=noisyEff(city,s,e,opt,rng,10),alts=altRatios(city,s,e,path,opt).filter(function(r){return r>=1.03&&r<=1.2;}).length;
  var cl=function(v){return v<0?0:v>1?1:v;};
  var simple=Math.min(hopEx,gEx); /* the better of the two obvious heuristics: if it is still well off the optimum, the map needs real planning */
  var score=.34*cl(simple/.07)+.12*cl(hopEx/.12)+.12*cl(gEx/.15)+.18*cl((.96-ease)/.22)+.12*cl((.995-noisy)/.07)+.12*cl(alts/3);
  return {s:s,e:e,opt:opt,hopEx:hopEx,gEx:gEx,simple:simple,ease:ease,noisy:noisy,alts:alts,score:score};
}
function pickPair(city,rng,tier,needCross,minSimple){
  var P=DIFF[city.diff],N=city.nodes,adj=city.adj,diagLen=Math.sqrt(W*W+H*H);
  var elig=N.filter(function(q){return !q.stub&&adj[q.id].length>=2&&q.x>=56&&q.x<=W-56;});
  if(!elig.length)return false;
  var cands=[];
  for(var a=0;a<18;a++){
    var s=elig[Math.floor(rng()*elig.length)],D=dijkstra(city,s.id),bp=bfsPrev(city,s.id);
    var cs=elig.filter(function(q){return q.id!==s.id&&sqd(q,s)>=P.minFrac*diagLen&&D.hops[q.id]>=P.minHops&&D.dist[q.id]<Infinity&&(!needCross||q.sd!==s.sd);});
    for(var b=0;b<5&&cs.length;b++){var q2=cs.splice(Math.floor(rng()*cs.length),1)[0];cands.push(pairMetrics(city,s.id,q2.id,D,bp,rng));}
  }
  if(!cands.length)return false;
  cands.sort(function(p,q){return p.score-q.score||p.s-q.s||p.e-q.e;});
  if(minSimple){var firm=cands.filter(function(m){return m.simple>=minSimple;});if(firm.length)cands=firm;} /* Journey levels guarantee a floor on difficulty */
  var pct=PICK_PCT[tier]!=null?PICK_PCT[tier]:.6,best=cands[Math.round(pct*(cands.length-1))];
  var D2=dijkstra(city,best.s);
  city.start=best.s;city.end=best.e;city.optimal={dist:D2.dist[best.e],path:pathTo(D2.prev,best.s,best.e)};city.metrics=best;
  return true;
}
/* Straight runs (3+ edges) of ordinary streets, used to make one-way streets that read as real streets. */
function streetRuns(city){
  var runs=[],cols=city.cols,rows=city.rows,i,j,cur;
  function flush(){if(cur.length>=3)runs.push(cur);cur=[];}
  for(j=0;j<rows;j++){cur=[];for(i=0;i<cols-1;i++){var e=edgeBetween(city,j*cols+i,j*cols+i+1);if(e&&e.type==='street'&&!e.bridge)cur.push(e);else flush();}flush();}
  for(i=0;i<cols;i++){cur=[];for(j=0;j<rows-1;j++){var e2=edgeBetween(city,j*cols+i,(j+1)*cols+i);if(e2&&e2.type==='street'&&!e2.bridge)cur.push(e2);else flush();}flush();}
  return runs;
}
var MAX_DETOUR=1.45; /* road rules may lengthen the best route by at most 45% */
/* Add roadworks / crashes (closed roads) and one-way streets. Keeps B reachable and the change meaningful (3%–45% longer).
   Returns false (and leaves the map unrestricted) if no fair arrangement is found. */
function applyRestrictions(city,rng,spec){
  var free=city.optimal,pe=[],i,t;
  for(i=1;i<free.path.length;i++)pe.push(edgeBetween(city,free.path[i-1],free.path[i]));
  var runs=streetRuns(city),onPath=new Set(pe);
  function clear(){city.edges.forEach(function(e){delete e.closed;delete e.ow;});}
  for(var attempt=0;attempt<40;attempt++){
    clear();var placed=0;
    for(var c=0;c<(spec.closures||0);c++){
      var kind=rng()<.5?'works':'crash',ok=false;
      for(t=0;t<14&&!ok;t++){
        var cand;
        if(rng()<.65&&pe.length>2)cand=pe[1+Math.floor(rng()*(pe.length-2))];
        else{var pa=free.path[Math.floor(rng()*free.path.length)],nbs=city.adj[pa];cand=nbs[Math.floor(rng()*nbs.length)].e;}
        if(cand.closed||cand.ow!=null||cand.a===city.start||cand.b===city.start||cand.a===city.end||cand.b===city.end)continue;
        cand.closed=kind;
        var Dc=dijkstra(city,city.start);
        if(isFinite(Dc.dist[city.end])&&Dc.dist[city.end]<=free.dist*MAX_DETOUR){ok=true;placed++;}else delete cand.closed;
      }
    }
    for(var o=0;o<(spec.oneway||0)&&runs.length;o++){
      var ok2=false;
      for(t=0;t<14&&!ok2;t++){
        var rel=runs.filter(function(r){return r.some(function(e){return onPath.has(e);});});
        var run=(rel.length&&rng()<.7)?rel[Math.floor(rng()*rel.length)]:runs[Math.floor(rng()*runs.length)];
        var len=Math.min(run.length,3+Math.floor(rng()*4)),st=Math.floor(rng()*(run.length-len+1)),seg=run.slice(st,st+len);
        if(seg.some(function(e){return e.closed||e.ow!=null;}))continue;
        var fwd=rng()<.5;
        if(rng()<.65){ /* point against the way the best route would use it, so the obvious road is forbidden */
          for(i=1;i<free.path.length;i++){var pe2=edgeBetween(city,free.path[i-1],free.path[i]);
            if(seg.indexOf(pe2)>=0){fwd=free.path[i-1]!==pe2.a;break;}}
        }
        seg.forEach(function(e){e.ow=fwd?e.a:e.b;});
        var Do=dijkstra(city,city.start);
        if(isFinite(Do.dist[city.end])&&Do.dist[city.end]<=free.dist*MAX_DETOUR){ok2=true;placed++;}else seg.forEach(function(e){delete e.ow;});
      }
    }
    var D=dijkstra(city,city.start),ratio=D.dist[city.end]/free.dist;
    if(placed>0&&isFinite(ratio)&&ratio>=1.03&&ratio<=MAX_DETOUR){
      city.optimalFree=free;city.optimal={dist:D.dist[city.end],path:pathTo(D.prev,city.start,city.end)};return true;
    }
  }
  clear();return false;
}
/* Map rule presets used by Practice (and the settings menu). tier: 1 easy … 3 hard. */
var RULE_SETS={
  classic:  {label:'Classic',  note:'The original maps. Nothing blocked.'},
  strategic:{label:'Strategic',note:'Rivers, dead ends and decoy shortcuts. No closures.'},
  roadworks:{label:'Roadworks',note:'Strategic maps with closed roads.'},
  oneway:   {label:'One-way',  note:'Strategic maps with one-way streets.'},
  mixed:    {label:'Mixed',    note:'Closures and one-way streets together.'}
};
function specFor(rules,diff){
  var t=diff==='easy'?1:diff==='medium'?2:3,sp={tier:t,river:0,riverP:1,closures:0,oneway:0};
  if(t===2){sp.river=3;sp.riverP=.6;}else if(t===3){sp.river=2;sp.riverP=.8;}
  if(rules==='roadworks')sp.closures=t;
  else if(rules==='oneway')sp.oneway=t;
  else if(rules==='mixed'){sp.closures=t===1?1:2;sp.oneway=t===1?1:2;}
  return sp;
}
/* strategic maps use a denser, more irregular network than classic ones (more shortcuts and missing links) */
var TIER_P={easy:{},medium:{remove:.17,diag:.22,avenues:2},hard:{remove:.2,diag:.28,avenues:3}};
function generateStrategic(seed,diff,spec){
  spec=spec||{};
  var tier=spec.tier||(diff==='easy'?1:diff==='medium'?2:3);
  var useRiver=spec.river>0&&(spec.riverP==null||mulberry32((seed^0x51ED270B)>>>0)()<spec.riverP);
  for(var k=0;k<24;k++){
    var s2=(seed+k*7919)>>>0,X={p:Object.assign({stubs:DIFF[diff].stubs+(spec.stubs||1)},TIER_P[diff],spec.p)};
    if(useRiver)X.river=spec.river;
    var c=tryGenerate(s2,diff,X);if(!c)continue;
    var rng=mulberry32((s2^0x7F4A7C15)>>>0);
    if(!pickPair(c,rng,tier,!!c.river,spec.minSimple))continue;
    c.optimalFree=c.optimal;
    if((spec.closures||spec.oneway)&&!applyRestrictions(c,rng,spec))continue;
    c.seed=seed;c.variant=k;c.spec=spec;return c;
  }
  throw new Error('strategic city generation failed');
}
function rulesPresent(city){
  var r={works:0,crash:0,oneway:0,bridge:0,river:!!city.river};
  city.edges.forEach(function(e){if(e.closed)r[e.closed]++;if(e.ow!=null)r.oneway++;if(e.bridge)r.bridge++;});
  return r;
}

/* ---- Journey: a fixed ladder of 15 maps. Each level is one deterministic map (same for everyone), introduced gradually. ---- */
var CHAPTERS=[
  {n:1,name:'Learner',  blurb:'Get a feel for the streets.'},
  {n:2,name:'Commuter', blurb:'Rivers and decoy shortcuts. Look before you turn.'},
  {n:3,name:'Roadworks',blurb:'Closed roads change the best way.'},
  {n:4,name:'One-Way',  blurb:'Streets with a direction. Follow the arrows.'},
  {n:5,name:'Rush Hour',blurb:'Everything at once.'}
];
var LEVELS=[
  {id:'L01',ch:1,title:'First Drive',      diff:'easy',  target:80,spec:{tier:1}},
  {id:'L02',ch:1,title:'Corner Shop',      diff:'easy',  target:85,spec:{tier:1}},
  {id:'L03',ch:1,title:'Back Streets',     diff:'easy',  target:88,spec:{tier:2,minSimple:.04}},
  {id:'L04',ch:2,title:'Across the River', diff:'medium',target:85,spec:{tier:2,river:3,riverP:1,minSimple:.05}},
  {id:'L05',ch:2,title:'Two Bridges',      diff:'medium',target:88,spec:{tier:2,river:2,riverP:1,minSimple:.05}},
  {id:'L06',ch:2,title:'Decoys',           diff:'medium',target:90,spec:{tier:3,river:3,riverP:1,minSimple:.08}},
  {id:'L07',ch:3,title:'Cones Ahead',      diff:'medium',target:85,spec:{tier:2,closures:1,minSimple:.04}},
  {id:'L08',ch:3,title:'Diversion',        diff:'medium',target:88,spec:{tier:2,river:3,riverP:1,closures:2,minSimple:.05}},
  {id:'L09',ch:3,title:'Gridlock',         diff:'hard',  target:88,spec:{tier:3,closures:3,minSimple:.05}},
  {id:'L10',ch:4,title:'This Way Only',    diff:'medium',target:85,spec:{tier:2,oneway:1,minSimple:.04}},
  {id:'L11',ch:4,title:'Arrows Everywhere',diff:'medium',target:88,spec:{tier:2,oneway:2,minSimple:.05}},
  {id:'L12',ch:4,title:'Riverside Loop',   diff:'hard',  target:88,spec:{tier:3,river:2,riverP:1,oneway:2,minSimple:.05}},
  {id:'L13',ch:5,title:'Rush Hour',        diff:'medium',target:88,spec:{tier:3,river:3,riverP:1,closures:1,oneway:1,minSimple:.08}},
  {id:'L14',ch:5,title:'City Centre',      diff:'hard',  target:88,spec:{tier:3,closures:2,oneway:2,minSimple:.06}},
  {id:'L15',ch:5,title:'The Wrong Way',    diff:'hard',  target:90,spec:{tier:3,river:2,riverP:1,closures:2,oneway:2,minSimple:.06}}
];
function levelById(id){for(var i=0;i<LEVELS.length;i++)if(LEVELS[i].id===id)return LEVELS[i];return null;}
function levelSeed(L){return hashString('wrongway:journey:'+L.id);}

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
    if(i>0){var bl=moveBlock(city,path[i-1],path[i]);
      if(bl==='none')return {ok:false,msg:'Your route uses a road that does not exist.'};
      if(bl==='closed')return {ok:false,msg:'Your route uses a closed road.'};
      if(bl==='oneway')return {ok:false,msg:'Your route goes the wrong way down a one-way street.'};}}
  if(path[path.length-1]!==city.end)return {ok:false,msg:"Your route hasn't reached B yet. Keep going from the glowing junction."};
  return {ok:true};
}
/* null when the move a→b is legal, otherwise why not: 'none' (no road), 'closed', 'oneway' */
function moveBlock(city,a,b){var e=edgeBetween(city,a,b);if(!e)return 'none';if(e.closed)return 'closed';if(e.ow!=null&&e.ow!==a)return 'oneway';return null;}

/* ---- scoring ----
   points = 1000 × (optimal ÷ yours)² is unchanged. One consistency rule is new: "perfect" means your distance is no longer than
   the optimal one (an exact integer comparison). Anything else is capped at 99.9% and 999 points, so a route that is a metre
   too long can never display 100.0% or 1,000. Labels and medals read the same rounded percentage the player sees. */
var MEDALS=[
  {key:'finish', name:'Finisher',min:0,  note:'Reached B'},
  {key:'bronze', name:'Bronze',  min:80, note:'80%+ efficiency'},
  {key:'silver', name:'Silver',  min:92, note:'92%+ efficiency'},
  {key:'gold',   name:'Gold',    min:98, note:'98%+ efficiency'},
  {key:'perfect',name:'Perfect', min:100,note:'Matched the optimal route'}
];
function medalFor(eff,perfect){return perfect?4:eff>=MEDALS[3].min?3:eff>=MEDALS[2].min?2:eff>=MEDALS[1].min?1:0;}
function resultLabel(eff,perfect){return perfect?'Perfect route':eff>=92?'Close enough':eff>=80?'Solid driving':eff>=60?'Took the scenic route':eff>=40?'Lost the plot':'Definitely the wrong way';}
function scoreRoute(city,path){
  var dist=routeDistance(city,path),opt=city.optimal.dist,perfect=dist<=opt;
  var exact=perfect?1:clamp(opt/dist,0,1);
  var eff=perfect?100:Math.min(99.9,Math.round(exact*1000)/10);
  var points=perfect?1000:Math.min(999,Math.round(1000*exact*exact));
  return {dist:dist,opt:opt,extra:Math.max(0,dist-opt),exact:exact,eff:eff,points:points,perfect:perfect,medal:medalFor(eff,perfect),
    turns:routeTurns(city,path),junctions:routeJunctions(city,path),label:resultLabel(eff,perfect)};
}
/* Where did the extra distance come from? For each step, "best possible total if I drive optimally from here" can only
   stay the same or grow. The growth at a step is the distance that decision cost. The steps add up to exactly dist − optimal,
   and it works with ties, closed roads and one-way streets because it uses the same legal network. */
function analyseRoute(city,path){
  var toEnd=city.toEnd||(city.toEnd=dijkstraTo(city,city.end)),cost=0,prevV=toEnd[path[0]],leaks=[];
  for(var i=1;i<path.length;i++){
    var e=edgeBetween(city,path[i-1],path[i]);cost+=e.w;
    var v=cost+toEnd[path[i]],lk=v-prevV;
    if(lk>0)leaks.push({step:i,node:path[i-1],to:path[i],leak:lk});
    prevV=v;
  }
  return leaks;
}
/*LOGIC-END*/

/* =====================================================================
   STORAGE
   ===================================================================== */
var STORE_KEY='thewrongway.v1',storageOK=true; /* unchanged key: saves from the previous version load and are upgraded in place */
var STORE_VER=2;
function own(o,k){return Object.prototype.hasOwnProperty.call(o,k);}
function defaults(){return {v:STORE_VER,settings:{theme:'dark',practiceDiff:'medium',hints:true,buildings:true,motion:'auto',sound:false,volume:0.7,rules:'strategic',traffic:true},daily:{},
  practice:{completed:0,totalEff:0,totalPoints:0,bestEff:0,bestScore:0,perfect:0,byDiff:{easy:0,medium:0,hard:0}},
  journey:{levels:{}},ach:{},seen:{},drafts:{}};}
function num(v,d){v=Number(v);return isFinite(v)?v:d;}
function okRoute(r){return Array.isArray(r)&&r.length>=1&&r.length<=800&&r.every(function(x){return Number.isInteger(x)&&x>=0&&x<5000;});}
function sanitize(o){
  var d=defaults();if(!o||typeof o!=='object')return d;
  var s=o.settings||{};
  d.settings.theme=s.theme==='light'?'light':'dark';
  d.settings.practiceDiff=own(DIFF,s.practiceDiff)?s.practiceDiff:'medium';
  d.settings.hints=s.hints!==false;d.settings.buildings=s.buildings!==false;d.settings.traffic=s.traffic!==false;
  d.settings.motion=(s.motion==='on'||s.motion==='off')?s.motion:'auto';
  d.settings.rules=own(RULE_SETS,s.rules)?s.rules:'strategic';
  d.settings.sound=s.sound===true;                                  /* sound is opt-in: only an explicit true enables it */
  d.settings.volume=Math.round(clamp(num(s.volume,0.7),0,1)*100)/100;
  if(o.daily&&typeof o.daily==='object'){Object.keys(o.daily).forEach(function(k){
    var r=o.daily[k];if(!/^\d{4}-\d{2}-\d{2}$/.test(k)||!r||typeof r!=='object')return;
    if(!okRoute(r.path))return;
    var dist=num(r.dist,0),opt=num(r.opt,0),eff=clamp(num(r.eff,0),0,100),pts=clamp(Math.round(num(r.points,0)),0,1000);
    if(opt>0&&dist>opt){eff=Math.min(eff,99.9);pts=Math.min(pts,999);} /* older saves could show 100.0% for a route a metre too long */
    d.daily[k]={seed:num(r.seed,0)>>>0,diff:own(DIFF,r.diff)?r.diff:'medium',path:r.path,dist:dist,opt:opt,eff:eff,points:pts,turns:num(r.turns,0)};});}
  var p=o.practice||{};
  d.practice.completed=Math.max(0,Math.floor(num(p.completed,0)));d.practice.totalEff=Math.max(0,num(p.totalEff,0));d.practice.totalPoints=Math.max(0,num(p.totalPoints,0));
  d.practice.bestEff=clamp(num(p.bestEff,0),0,100);d.practice.bestScore=clamp(num(p.bestScore,0),0,1000);d.practice.perfect=Math.max(0,Math.floor(num(p.perfect,0)));
  if(!d.practice.perfect){d.practice.bestEff=Math.min(d.practice.bestEff,99.9);d.practice.bestScore=Math.min(d.practice.bestScore,999);} /* no perfect route recorded, so a stored 100% cannot be right */
  var b=p.byDiff||{};['easy','medium','hard'].forEach(function(k){d.practice.byDiff[k]=Math.max(0,Math.floor(num(b[k],0)));});
  var jl=(o.journey&&o.journey.levels&&typeof o.journey.levels==='object')?o.journey.levels:{};
  LEVELS.forEach(function(L){var r=own(jl,L.id)?jl[L.id]:null;if(!r||typeof r!=='object')return;
    d.journey.levels[L.id]={done:r.done===true,best:clamp(num(r.best,0),0,100),pts:clamp(Math.round(num(r.pts,0)),0,1000),medal:clamp(Math.floor(num(r.medal,0)),0,4),tries:Math.max(0,Math.floor(num(r.tries,0))),perfect:r.perfect===true};});
  [['ach',function(v){return num(v,1);}],['seen',function(){return true;}]].forEach(function(t){
    var src=o[t[0]];if(src&&typeof src==='object')Object.keys(src).forEach(function(k){if(/^[a-z0-9]{1,24}$/.test(k)&&src[k])d[t[0]][k]=t[1](src[k]);});});
  var dr=o.drafts||{};
  if(dr.daily&&/^\d{4}-\d{2}-\d{2}$/.test(dr.daily.key)&&okRoute(dr.daily.route))d.drafts.daily={key:dr.daily.key,route:dr.daily.route};
  if(dr.practice&&okRoute(dr.practice.route)&&own(DIFF,dr.practice.diff)&&own(RULE_SETS,dr.practice.rules))
    d.drafts.practice={seed:num(dr.practice.seed,0)>>>0,diff:dr.practice.diff,rules:dr.practice.rules,route:dr.practice.route,counted:dr.practice.counted!==false};
  if(dr.journey&&typeof dr.journey.id==='string'&&levelById(dr.journey.id)&&okRoute(dr.journey.route))d.drafts.journey={id:dr.journey.id,route:dr.journey.route};
  return d;
}
function readDisk(){var raw;try{raw=localStorage.getItem(STORE_KEY);}catch(e){storageOK=false;return null;}
  if(!raw)return null;try{return sanitize(JSON.parse(raw));}catch(e){return null;}} /* unreadable JSON is replaced on the next save; storage itself still works */
var S=(function(){var d=readDisk();return d||defaults();})();
function save(){try{S.v=STORE_VER;localStorage.setItem(STORE_KEY,JSON.stringify(S));}catch(e){storageOK=false;}}
/* Every change goes through commit(): it re-reads what is on disk right now (another tab may have written since this page loaded),
   applies the change to that fresh copy, then saves. Two tabs can no longer overwrite each other's results. */
function commit(fn){var base=readDisk()||S;fn(base);S=base;save();}

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
    arrive:{gap:150,pri:1},submit:{pri:1},optimal:{pri:1},on:{pri:1},off:{pri:1},
    blocked:{gap:260},medal:{pri:1},pb:{pri:1},unlock:{pri:1}
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
    modal:function(t){tone(t,{f:420,to:560,a:.002,d:.07,v:.18});},
    blocked:function(t,j){ /* closed road / wrong way down a one-way street: a short, dull thunk (clearly not the error blips) */
      tone(t,{f:150,to:92,type:'triangle',a:.002,d:.11,v:.22,lp:700,j:j});
      noise(t,{type:'lowpass',f:1100,to:300,q:.7,a:.002,d:.07,v:.09});
    },
    medal:function(t,j,o){ /* 1 = bronze … 3 = gold: a rising run with one more note per tier */
      var tier=clamp((o&&o.tier)||1,1,3),n=[523.25,659.25,783.99,1046.5],i;
      for(i=0;i<=tier;i++){tone(t+i*.085,{f:n[i],type:'triangle',a:.004,d:.2+i*.04,v:.12});tone(t+i*.085,{f:n[i]*2,a:.004,d:.12,v:.03});}
    },
    pb:function(t){ /* personal best: two bright notes and a little sparkle */
      tone(t,{f:1174.7,type:'triangle',a:.003,d:.12,v:.1});
      tone(t+.08,{f:1760,type:'triangle',a:.003,d:.22,v:.1});
      noise(t+.08,{type:'highpass',f:7000,a:.005,d:.14,v:.025});
    },
    unlock:function(t){tone(t,{f:783.99,type:'triangle',a:.004,d:.12,v:.1});tone(t+.07,{f:987.77,type:'triangle',a:.004,d:.12,v:.1});tone(t+.14,{f:1318.5,type:'triangle',a:.004,d:.26,v:.11});}
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
  function fire(name,opt){
    var j=1+(Math.random()*2-1)*.025;
    FX[name](ctx.currentTime+.006,j,opt);
  }
  function play(name,opt){
    try{
      var force=!!(opt&&opt.force);
      if(!ctx||!FX[name]||!(force||enabled()))return;
      var now=performance.now();
      if(!allow(name,now))return;
      if(ctx.state==='running'){fire(name,opt);return;}
      /* Suspended (idle tab, iOS interruption): try to wake it, and only play if that happens right away.
         Never schedule while suspended, or sounds would pile up and fire together on resume. */
      Promise.resolve(ctx.resume()).then(function(){if(ctx.state==='running'&&performance.now()-now<250)fire(name,opt);},function(){});
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
var G={view:'home',nav:'home',navLevel:null,mode:'daily',diff:'medium',rules:'classic',level:null,city:null,seed:0,dateKey:'',route:[],locked:false,result:null,review:false,counted:true,anim:0,u:1,refs:null,drag:null,toastT:0,
  firstRes:null,leaks:null,skip:null,draftT:0,info:null};
var svg=$('mapSvg');

/* =====================================================================
   MAP RENDERING
   ===================================================================== */
/* ---- street names: shown on the big roads only, as quiet map labels ---- */
var ST_NAMES=['Maple','Harbour','Elm','Station','Mill','Orchard','Bridge','Castle','Market','Abbey','Forge','Willow','King','Queen','Park','Quarry','Chapel','Cedar','Lime','Vine','Beacon','Anchor','Baker','Cross','Ferry','Granary','Hill','Jubilee','Lantern','Meadow','Nelson','Oak','Priory','Quay','Rose','Salt','Tannery','Union','Victoria','Wharf'];
function mainRuns(city){ /* straight runs of arterial roads, and chains of avenues, as lists of junction ids */
  var out=[],cols=city.cols,rows=city.rows,i,j,cur=[];
  function isArt(a,b){var e=edgeBetween(city,a,b);return !!e&&e.type==='arterial';}
  function flush(k){if(cur.length>=4)out.push({ids:cur,kind:k});cur=[];}
  for(j=0;j<rows;j++){cur=[];for(i=0;i<cols-1;i++){var a=j*cols+i;if(isArt(a,a+1)){if(!cur.length)cur.push(a);cur.push(a+1);}else flush('h');}flush('h');}
  for(i=0;i<cols;i++){cur=[];for(j=0;j<rows-1;j++){var b=j*cols+i;if(isArt(b,b+cols)){if(!cur.length)cur.push(b);cur.push(b+cols);}else flush('v');}flush('v');}
  var av=city.edges.filter(function(e){return e.type==='avenue';}),byNode={},seen=new Set();
  av.forEach(function(e){(byNode[e.a]=byNode[e.a]||[]).push(e);(byNode[e.b]=byNode[e.b]||[]).push(e);});
  function nextFree(n){return (byNode[n]||[]).filter(function(q){return !seen.has(q);})[0];}
  av.forEach(function(e0){
    if(seen.has(e0))return;seen.add(e0);
    var chain=[e0],front=e0.b,back=e0.a,x;
    while((x=nextFree(front))){seen.add(x);chain.push(x);front=x.a===front?x.b:x.a;}
    while((x=nextFree(back))){seen.add(x);chain.unshift(x);back=x.a===back?x.b:x.a;}
    var ids=[back],c=back;chain.forEach(function(e){c=e.a===c?e.b:e.a;ids.push(c);});
    if(ids.length>=4)out.push({ids:ids,kind:'d'});
  });
  return out;
}
function labelsHTML(city,uid){
  var N=city.nodes,rng=mulberry32((city.seed^0x27D4EB2F)>>>0),pool=ST_NAMES.slice(),i;
  for(i=pool.length-1;i>0;i--){var r=Math.floor(rng()*(i+1)),t=pool[i];pool[i]=pool[r];pool[r]=t;}
  var suf={h:['Avenue','Road','Way'],v:['Street','Lane','Row'],d:['Parade','Mile','Drive']};
  var clear=function(run){for(var q=1;q<run.ids.length;q++){var e=edgeBetween(city,run.ids[q-1],run.ids[q]);if(!e||e.closed||e.bridge)return false;}return true;}; /* names never sit on closed roads or bridges */
  var runs=mainRuns(city).filter(clear).sort(function(a,b){return b.ids.length-a.ids.length;}).slice(0,6),defs='',txt='';
  runs.forEach(function(run,ix){
    var pts=run.ids.map(function(id){return N[id];}),ang=Math.atan2(pts[pts.length-1].y-pts[0].y,pts[pts.length-1].x-pts[0].x);
    if(ang>Math.PI/2||ang<=-Math.PI/2)pts=pts.slice().reverse();
    var len=0;for(i=1;i<pts.length;i++)len+=sqd(pts[i-1],pts[i]);
    var d='M'+pts.map(function(q){return f(q.x)+' '+f(q.y);}).join('L'),name=(pool[ix%pool.length]+' '+suf[run.kind][ix%3]).toUpperCase(),id='lp-'+uid+'-'+ix;
    defs+='<path id="'+id+'" d="'+d+'"/>';
    txt+='<text class="st-name" data-len="'+len.toFixed(1)+'"><textPath href="#'+id+'" startOffset="50%" text-anchor="middle">'+name+'</textPath></text>';
  });
  return '<defs>'+defs+'</defs>'+txt;
}
function smoothD(pts){ /* Catmull-Rom through the points, as cubic Béziers */
  var d='M'+f(pts[0].x)+' '+f(pts[0].y);
  for(var i=0;i<pts.length-1;i++){
    var p0=pts[i-1]||pts[i],p1=pts[i],p2=pts[i+1],p3=pts[i+2]||p2;
    d+='C'+f(p1.x+(p2.x-p0.x)/6)+' '+f(p1.y+(p2.y-p0.y)/6)+' '+f(p2.x-(p3.x-p1.x)/6)+' '+f(p2.y-(p3.y-p1.y)/6)+' '+f(p2.x)+' '+f(p2.y);
  }
  return d;
}
function markerHTML(kind,node){
  var color=kind==='A'?'var(--start)':'var(--end)',label=kind==='A'?'START':'FINISH',pw=kind==='A'?66:78;
  var pin='M0 0C-4-8-17-16-17-29A17 17 0 1 1 17-29C17-16 4-8 0 0Z';
  var icon=kind==='A'?'<path class="mk-ic" d="M9 -4.6L16 0L9 4.6Z"/>'
    :'<g class="mk-ic"><rect x="9" y="-3.8" width="3.8" height="3.8"/><rect x="16.6" y="-3.8" width="3.8" height="3.8"/><rect x="12.8" y="0" width="3.8" height="3.8"/><rect x="20.4" y="0" width="3.8" height="3.8"/></g>';
  var tx=pw/2+(kind==='A'?8:11);
  return '<g class="mk mk-'+kind+'" data-x="'+f(node.x)+'" data-y="'+f(node.y)+'" data-w="'+pw+'" style="--c:'+color+'">'+
    '<circle class="mk-zone" r="'+(kind==='A'?19:22)+'"/>'+
    '<circle class="mk-ring" r="13" stroke="'+color+'"/>'+
    '<g class="mk-flip"><g class="mk-pin"><path d="'+pin+'" fill="'+color+'" stroke="var(--map-bg)" stroke-width="2"/></g></g>'+
    '<text class="mk-letter" x="0" y="-29">'+kind+'</text>'+
    '<g class="mk-lab"><rect class="mk-pill" x="0" y="-11" width="'+pw+'" height="22" rx="11"/>'+icon+
    '<text class="mk-text" x="'+tx+'" y="0" text-anchor="middle">'+label+'</text></g></g>';
}
/* A top-down car facing +x, about 26 × 13 map units. cls decides the role (hero, racer, traffic). */
function carHTML(cls,extra,style){
  return '<g class="'+cls+'" style="'+(style==null?'display:none':style)+'"><g class="car-in">'+(extra||'')+
    '<rect class="car-sh" x="-12" y="-4.4" width="26" height="13" rx="5"/>'+
    '<rect class="car-wh" x="-9.4" y="-7.4" width="5" height="1.9" rx=".8"/><rect class="car-wh" x="-9.4" y="5.5" width="5" height="1.9" rx=".8"/>'+
    '<rect class="car-wh" x="5.2" y="-7.4" width="5" height="1.9" rx=".8"/><rect class="car-wh" x="5.2" y="5.5" width="5" height="1.9" rx=".8"/>'+
    '<path class="car-body" d="M-13 -4.6Q-13 -6.2 -11 -6.2L7 -6.2Q11 -6.2 12.6 -3.2Q13.4 -1.6 13.4 0Q13.4 1.6 12.6 3.2Q11 6.2 7 6.2L-11 6.2Q-13 6.2 -13 4.6Z"/>'+
    '<path class="car-glass" d="M2.4 -4.7L6.2 -4Q7.2 0 6.2 4L2.4 4.7Z"/><path class="car-glass" d="M-9 -4.3L-6.2 -4.5L-6.2 4.5L-9 4.3Z"/>'+
    '<rect class="car-roof" x="-5.8" y="-4.6" width="8" height="9.2" rx="1.9"/>'+
    '<rect class="car-hl" x="11.4" y="-4.9" width="1.8" height="2.2" rx=".6"/><rect class="car-hl" x="11.4" y="2.7" width="1.8" height="2.2" rx=".6"/>'+
    '<rect class="car-tl" x="-13.1" y="-4.9" width="1.6" height="2.2" rx=".6"/><rect class="car-tl" x="-13.1" y="2.7" width="1.6" height="2.2" rx=".6"/>'+
    '</g></g>';
}
function buildMapSVG(el,city,o){
  var N=city.nodes,p=[],cols=city.cols,uid=el.id||'m';
  function has(a,b){return city.emap.has(edgeKey(a,b));}
  function inset(P){var cx=0,cy=0;P.forEach(function(q){cx+=q.x;cy+=q.y;});cx/=P.length;cy/=P.length;return P.map(function(q){return {x:cx+(q.x-cx)*.88,y:cy+(q.y-cy)*.88};});}
  function poly(P){return 'M'+P.map(function(q){return f(q.x)+' '+f(q.y);}).join('L')+'Z';}
  /* rd keeps its original call order so block, park and building layout is unchanged; rd2 drives the newer details (tone, trees) */
  var rd=mulberry32((city.seed^0x9E3779B9)>>>0),rd2=mulberry32((city.seed^0x85EBCA6B)>>>0),blocks=[],parks=[],blds=[],blds2=[],trees=[];
  for(var j=0;j<city.rows-1;j++)for(var i=0;i<cols-1;i++){
    var a=j*cols+i,b=a+1,c=a+cols+1,d=a+cols;
    if(!(has(a,b)&&has(b,c)&&has(d,c)&&has(a,d)))continue;
    var A=N[a],B=N[b],C=N[c],D=N[d];
    if(has(a,c)){blocks.push(poly(inset([A,B,C])),poly(inset([A,C,D])));continue;}
    if(has(b,d)){blocks.push(poly(inset([A,B,D])),poly(inset([B,C,D])));continue;}
    var park=rd()<.08;
    (park?parks:blocks).push(poly(inset([A,B,C,D])));
    var bil=function(u,v){return {x:(1-u)*(1-v)*A.x+u*(1-v)*B.x+u*v*C.x+(1-u)*v*D.x,y:(1-u)*(1-v)*A.y+u*(1-v)*B.y+u*v*C.y+(1-u)*v*D.y};};
    if(park&&o.buildings!==false){
      for(var tn=0;tn<5;tn++){var tp=bil(.2+rd2()*.6,.2+rd2()*.6),tr=3.6+rd2()*2.6;
        trees.push('M'+f(tp.x-tr)+' '+f(tp.y)+'a'+f(tr)+' '+f(tr)+' 0 1 0 '+f(2*tr)+' 0a'+f(tr)+' '+f(tr)+' 0 1 0 '+f(-2*tr)+' 0Z');}
    }
    for(var sa=0;sa<2;sa++)for(var sb=0;sb<2;sb++){
      var skip=rd()<.28,u0=sa*.5+.14+rd()*.07,u1=sa*.5+.5-.06-rd()*.07,v0=sb*.5+.14+rd()*.07,v1=sb*.5+.5-.06-rd()*.07;
      if(skip||park||!o.buildings)continue;
      (rd2()<.32?blds2:blds).push(poly([bil(u0,v0),bil(u1,v0),bil(u1,v1),bil(u0,v1)]));
    }
  }
  p.push('<rect class="m-bg" x="0" y="0" width="'+W+'" height="'+H+'"/>');
  if(city.river){
    var rv=smoothD(city.river.pts);
    p.push('<g class="l-water"><path class="wt-shore" d="'+rv+'" stroke-width="'+(city.river.w+12)+'"/><path class="wt" d="'+rv+'" stroke-width="'+city.river.w+'"/><path class="wt-hi" d="'+rv+'" stroke-width="'+Math.round(city.river.w*.5)+'"/></g>');
  }
  var bsh=blds.concat(blds2).join('');
  p.push('<g class="l-blocks"><path class="blk" d="'+blocks.join('')+'"/><path class="park" d="'+parks.join('')+'"/>'+
    (bsh?'<path class="bld-sh" transform="translate(2.2 3)" d="'+bsh+'"/>':'')+'<path class="bld" d="'+blds.join('')+'"/><path class="bld bld2" d="'+blds2.join('')+'"/><path class="tree" d="'+trees.join('')+'"/></g>');
  var dS=[],dM=[],dB=[],dCW=[],dCC=[],owH='',rwH='',e0;
  city.edges.forEach(function(e){var A=N[e.a],B=N[e.b],s='M'+f(A.x)+' '+f(A.y)+'L'+f(B.x)+' '+f(B.y),main=(e.type==='arterial'||e.type==='avenue');
    (main?dM:dS).push(s);if(e.bridge)dB.push(s);
    if(e.closed){(e.closed==='crash'?dCC:dCW).push(s);
      var mx=(A.x+B.x)/2,my=(A.y+B.y)/2,an=Math.atan2(B.y-A.y,B.x-A.x)*180/Math.PI;
      rwH+=e.closed==='crash'
        ?'<g class="rw rw-crash" data-x="'+f(mx)+'" data-y="'+f(my)+'" data-a="'+f(an)+'"><title>Accident: road closed</title><path class="rw-tri" d="M0 -10L10 7H-10Z"/><path class="rw-bang" d="M0 -4V1.5M0 4.4V4.5"/><circle class="rw-beacon" cx="-9" cy="-8" r="2.6"/><circle class="rw-beacon b2" cx="9" cy="-8" r="2.6"/></g>'
        :'<g class="rw rw-works" data-x="'+f(mx)+'" data-y="'+f(my)+'" data-a="'+f(an)+'"><title>Roadworks: road closed</title><path class="rw-cone" d="M-8.5 -10.5l2.6 5.6h-5.2z"/><path class="rw-cone" d="M-8.5 10.5l2.6 -5.6h-5.2z"/><rect class="rw-bar" x="-2.6" y="-8.4" width="5.2" height="16.8" rx="1.3"/><path class="rw-sl" d="M-2.6 -5.2L2.6 -8M-2.6 0.4L2.6 -2.4M-2.6 6L2.6 3.2"/></g>';
    }
    if(e.ow!=null){var F=N[e.ow],T=N[e.ow===e.a?e.b:e.a],ang=Math.atan2(T.y-F.y,T.x-F.x)*180/Math.PI,ln=e.len,fr=ln>86?[.32,.68]:[.5];
      fr.forEach(function(t){owH+='<g class="ow" data-x="'+f(F.x+(T.x-F.x)*t)+'" data-y="'+f(F.y+(T.y-F.y)*t)+'" data-a="'+f(ang)+'"><title>One-way street</title><path class="ow-ch" d="M-3.6 -3.8L1.8 0L-3.6 3.8"/></g>';});}
  });
  p.push('<g class="l-roads"><path class="rd-case" d="'+dS.join('')+'"/><path class="rdm-case" d="'+dM.join('')+'"/>'+(dB.length?'<path class="br-case" d="'+dB.join('')+'"/>':'')+
    '<path class="rd" d="'+dS.join('')+'"/><path class="rd-main" d="'+dM.join('')+'"/><path class="rd-lane" d="'+dS.join('')+'"/><path class="rd-mid" d="'+dM.join('')+'"/>'+
    (dCW.length||dCC.length?'<g class="l-closed"><path class="cl-case" d="'+dCW.concat(dCC).join('')+'"/><path class="cl-works" d="'+dCW.join('')+'"/><path class="cl-crash" d="'+dCC.join('')+'"/></g>':'')+'</g>');
  if(owH)p.push('<g class="l-ow" pointer-events="none">'+owH+'</g>');
  var bulbs='',nd='';
  N.forEach(function(q){var dg=city.adj[q.id].length;
    if(dg===1)bulbs+='<circle class="bulb-case" cx="'+f(q.x)+'" cy="'+f(q.y)+'"/><circle class="bulb" cx="'+f(q.x)+'" cy="'+f(q.y)+'"/>';
    nd+='<circle class="nd '+(dg===1?'nd1':dg===2?'nd2':'nd3')+'" cx="'+f(q.x)+'" cy="'+f(q.y)+'" r="3"/>';});
  p.push('<g class="l-bulbs">'+bulbs+'</g><g class="l-nodes">'+nd+'</g>');
  p.push('<g class="l-labels" pointer-events="none">'+labelsHTML(city,uid)+'</g>');
  p.push('<g class="l-traffic" pointer-events="none"></g>');
  p.push('<g class="l-opt"><path class="opt-glow" pathLength="1000" d=""/><path class="opt" pathLength="1000" d=""/></g>');
  p.push('<g class="l-route"><path class="route-glow" d=""/><path class="route-main" d=""/><path class="route-last" d=""/></g>');
  p.push('<g class="l-rw" pointer-events="none">'+rwH+'</g>');
  p.push('<path class="hover-seg" d=""/><g class="l-hints"></g><g class="l-end"></g><g class="l-detours" pointer-events="none"></g>');
  p.push(carHTML('l-car','<path class="car-beam" d="M13 -4.4L38 -11L38 11L13 4.4Z"/>'));
  p.push(carHTML('l-car2'));
  p.push('<g class="l-markers" pointer-events="none">'+markerHTML('A',N[city.start])+markerHTML('B',N[city.end])+'</g>');
  el.innerHTML=p.join('');
}
function applyScale(el){
  var w=el.getBoundingClientRect().width||W,u=W/w,i,k;
  el.style.setProperty('--u',u.toFixed(4));
  el.classList.toggle('compact',u>1.9);
  var cs=el.querySelectorAll('.nd');
  for(i=0;i<cs.length;i++){var c=cs[i];c.setAttribute('r',((c.classList.contains('nd1')?2.2:c.classList.contains('nd2')?1.8:3)*u).toFixed(2));}
  var bb=el.querySelectorAll('.bulb'),bc=el.querySelectorAll('.bulb-case');
  for(i=0;i<bb.length;i++){bb[i].setAttribute('r',(4.6*u).toFixed(2));bc[i].setAttribute('r',(6.1*u).toFixed(2));}
  var m=clamp(u*.95,1,2.1),mk=el.querySelectorAll('.mk');
  for(k=0;k<mk.length;k++){
    var g=mk[k],x=+g.dataset.x,y=+g.dataset.y,pw=+g.dataset.w,flip=y-66*m<6,right=x+(26+pw)*m+10<W;
    g.setAttribute('transform','translate('+g.dataset.x+' '+g.dataset.y+') scale('+m.toFixed(3)+')');
    g.querySelector('.mk-flip').setAttribute('transform',flip?'scale(1,-1)':'');
    g.querySelector('.mk-letter').setAttribute('y',flip?29:-29);
    g.querySelector('.mk-lab').setAttribute('transform','translate('+(right?26:-26-pw)+' '+(flip?29:-29)+')');
  }
  function place(sel,scale){var L=el.querySelectorAll(sel);for(var q=0;q<L.length;q++){var t=L[q];t.setAttribute('transform','translate('+t.dataset.x+' '+t.dataset.y+')'+(t.dataset.a!==undefined?' rotate('+t.dataset.a+')':'')+' scale('+scale.toFixed(3)+')');}}
  place('.ow',u*.95);place('.rw',m);place('.dt',m);
  ['.l-car','.l-car2','.l-traffic'].forEach(function(sel){var cc=el.querySelector(sel);if(cc)cc.dataset.m=clamp(u*.9,1,2).toFixed(3);});
  var lb=el.querySelectorAll('.st-name');
  for(i=0;i<lb.length;i++){ /* hide a label that would not fit along its road at this size */
    var t2=lb[i];t2.style.display='';var tl=0;try{tl=t2.getComputedTextLength();}catch(e){}
    if(tl>0&&tl>+t2.dataset.len*.92)t2.style.display='none';
  }
  return u;
}
function grabRefs(){var q=function(s){return svg.querySelector(s);};
  G.refs={glow:q('.route-glow'),main:q('.route-main'),last:q('.route-last'),hover:q('.hover-seg'),hints:q('.l-hints'),end:q('.l-end'),opt:q('.opt'),optGlow:q('.opt-glow'),car:q('.l-car'),car2:q('.l-car2'),det:q('.l-detours'),traffic:q('.l-traffic')};}

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
  r.end.innerHTML=G.locked?'':'<circle class="end-ring" cx="'+f(e.x)+'" cy="'+f(e.y)+'" r="'+f(9*u)+'"/>'+(animLast&&!reduceMotion()?'<circle class="pop" cx="'+f(e.x)+'" cy="'+f(e.y)+'" r="'+f(9*u)+'"/>':'');
  var h='';
  if(!G.locked&&endId!==c.end&&S.settings.hints){c.adj[endId].forEach(function(nb){if(R.indexOf(nb.to)>=0||!canGo(nb.e,endId))return;var q=N[nb.to];h+='<circle class="hint" cx="'+f(q.x)+'" cy="'+f(q.y)+'" r="'+f(6.5*u)+'"/>';});}
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
  $('hStatus').textContent=R.length===1?'AT START':atB?'REACHED B':deadEnd(c,R)?'DEAD END':'EN ROUTE';
  $('undoBtn').disabled=G.locked||R.length<=1;$('clearBtn').disabled=G.locked||R.length<=1;
  $('resetBtn').disabled=G.locked;$('submitBtn').disabled=G.locked;$('submitBtn').classList.toggle('ready',atB&&!G.locked);
}
function toast(msg,kind,ms){var t=G.view==='game'?$('toast'):$('gToast'),o=t===$('toast')?$('gToast'):$('toast');o.classList.remove('show');t.textContent=msg;t.className='toast show '+(kind||'info');clearTimeout(G.toastT);G.toastT=setTimeout(function(){t.classList.remove('show');},ms||(kind==='error'?5200:3200));}
function refresh(animLast){renderRoute(animLast);updateHUD();}
function focusMap(){try{svg.focus({preventScroll:true});}catch(e){}}
/* a junction you cannot drive on from (everything ahead is closed, one-way the wrong way, or already on your route) */
function deadEnd(c,R){var end=R[R.length-1];if(end===c.end)return false;return !c.adj[end].some(function(nb){return canGo(nb.e,end)&&R.indexOf(nb.to)<0;});}
/* in-progress routes are saved, so a refresh, a Back swipe or switching mode never loses the drawing */
function persistSoon(){clearTimeout(G.draftT);G.draftT=setTimeout(writeDraft,260);}
function flushDraft(){if(G.draftT){clearTimeout(G.draftT);writeDraft();}}
function writeDraft(){
  G.draftT=0;if(!G.city||G.locked||G.review)return;
  var mode=G.mode,R=G.route.slice(),lid=G.level?G.level.id:null,dk=G.dateKey,sd=G.seed,df=G.diff,ru=G.rules,ct=G.counted;
  commit(function(s){
    if(mode==='daily'){if(R.length>1)s.drafts.daily={key:dk,route:R};else delete s.drafts.daily;}
    else if(mode==='journey'){if(R.length>1&&lid)s.drafts.journey={id:lid,route:R};else if(s.drafts.journey&&s.drafts.journey.id===lid)delete s.drafts.journey;}
    else s.drafts.practice={seed:sd,diff:df,rules:ru,route:R,counted:ct};
  });
}
function validDraftRoute(c,R){
  if(!Array.isArray(R)||!R.length||R[0]!==c.start)return false;
  var seen=new Set([R[0]]);
  for(var i=1;i<R.length;i++){if(R[i]>=c.nodes.length||seen.has(R[i])||moveBlock(c,R[i-1],R[i])!==null)return false;if(R[i-1]===c.end)return false;seen.add(R[i]);}
  return true;
}

function tryAdd(id,silent){
  if(G.locked)return 'locked';
  var c=G.city,R=G.route,end=R[R.length-1];
  if(id===end)return 'same';
  if(R.length>1&&id===R[R.length-2]){R.pop();refresh(false);persistSoon();Sound.play('undo');return 'back';}
  var bl=moveBlock(c,end,id);
  if(bl==='none'){if(!silent){toast("That junction isn't connected to your position. Pick a ringed intersection.",'error');Sound.play('error');}return 'invalid';}
  if(end===c.end){if(!silent){toast("You've reached B. Submit your route, or undo to change it.",'good');Sound.play('tap');}return 'done';}
  if(bl==='closed'){var ce=edgeBetween(c,end,id);if(!silent){toast(ce.closed==='crash'?'Accident ahead. That road is closed.':'Roadworks ahead. That road is closed.','error');Sound.play('blocked');}return 'blocked';}
  if(bl==='oneway'){if(!silent){toast('One-way street. You can only drive it the way the arrows point.','error');Sound.play('blocked');}return 'blocked';}
  if(R.indexOf(id)>=0){if(!silent){toast("Your route can't cross itself. Undo to back up first.",'error');Sound.play('error');}return 'loop';}
  R.push(id);refresh(true);persistSoon();
  if(id===c.end){toast("You've reached B! Submit your route when you're ready.",'good');Sound.play('arrive');}
  else{Sound.play('snap');if(deadEnd(c,R))toast('Dead end. Nothing to drive on from here. Undo to back up.','info');}
  return 'added';
}
function undo(){if(G.locked||G.route.length<=1)return false;G.route.pop();refresh(false);persistSoon();Sound.play('undo');return true;}
function clearRoute(){if(G.locked||G.route.length<=1)return;G.route=[G.city.start];refresh(false);persistSoon();Sound.play('clear');toast('Route cleared. Start again from A.','info');}
async function resetBoard(){
  if(G.review||G.locked)return;
  if(G.route.length-1>=3){var cty=G.city,ok=await confirmBox('Reset this challenge?','Your drawn route will be removed. The map and its pins stay exactly the same.','Reset');if(!ok||G.locked||G.city!==cty)return;}
  G.route=[G.city.start];G.refs.hover.setAttribute('d','');refresh(false);persistSoon();Sound.play('clear');toast('Challenge reset.','info');
}

/* pointer input */
function svgPt(ev){var p=svg.createSVGPoint();p.x=ev.clientX;p.y=ev.clientY;var m=svg.getScreenCTM();return m?p.matrixTransform(m.inverse()):{x:0,y:0};}
function nearest(p,radius,filter){var best=-1,bd=radius,N=G.city.nodes;for(var i=0;i<N.length;i++){if(filter&&!filter(i))continue;var d=Math.hypot(N[i].x-p.x,N[i].y-p.y);if(d<bd){bd=d;best=i;}}return best;}
function legalSet(){var R=G.route,end=R[R.length-1],s=new Set([end]);if(R.length>1)s.add(R[R.length-2]);G.city.adj[end].forEach(function(nb){if(canGo(nb.e,end))s.add(nb.to);});return s;}
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
  else if(G.drag&&G.drag.warn!==id){var bl=moveBlock(G.city,end,id);if(bl==='closed'||bl==='oneway'){G.drag.warn=id;tryAdd(id,false);}} /* tell the player once why a road won't take them */
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
/* ---- achievements: small milestones, checked after every result ---- */
function journeyDoneCount(){return LEVELS.filter(function(L){var r=S.journey.levels[L.id];return r&&r.done;}).length;}
function levelStars(L){var r=S.journey.levels[L.id];if(!r||!r.done)return 0;return 1+(r.best>=L.target?1:0)+(r.perfect?1:0);}
function journeyStars(){return LEVELS.reduce(function(n,L){return n+levelStars(L);},0);}
function chapterDone(n){return LEVELS.filter(function(L){return L.ch===n;}).every(function(L){var r=S.journey.levels[L.id];return r&&r.done;});}
var ACH=[
  {id:'first',   name:'First Drive',      desc:'Complete any challenge.',                              test:function(c){return c.A.total>=1;}},
  {id:'streak3', name:'On a Roll',        desc:'Complete the Daily three days in a row.',               test:function(c){return c.A.longest>=3;}},
  {id:'streak7', name:'Regular',          desc:'Keep a 7-day Daily streak.',                            test:function(c){return c.A.longest>=7;}},
  {id:'silver',  name:'Podium Finish',    desc:'Earn a Silver medal or better.',                        test:function(c){return c.res.medal>=2;}},
  {id:'gold',    name:'Sharp Eye',        desc:'Earn a Gold medal (98%+).',                             test:function(c){return c.res.medal>=3;}},
  {id:'perfect', name:'Flawless',         desc:'Drive a perfect route.',                                test:function(c){return c.res.perfect;}},
  {id:'perfect5',name:'Cartographer',     desc:'Drive five perfect routes.',                            test:function(c){return c.A.perfect>=5;}},
  {id:'hard90',  name:'Hard Hitter',      desc:'Reach 90% or better on a Hard map.',                    test:function(c){return c.diff==='hard'&&c.res.eff>=90;}},
  {id:'bridge',  name:'Bridge Builder',   desc:'Earn Silver or better on a map with a river.',          test:function(c){return c.res.medal>=2&&c.rp.river;}},
  {id:'works',   name:'Cone Zone',        desc:'Earn Silver or better on a map with closed roads.',     test:function(c){return c.res.medal>=2&&(c.rp.works+c.rp.crash)>0;}},
  {id:'oneway',  name:'Right Way Round',  desc:'Earn Silver or better on a map with one-way streets.',  test:function(c){return c.res.medal>=2&&c.rp.oneway>0;}},
  {id:'ch3',     name:'Roadworker',       desc:'Finish Journey chapter 3.',                             test:function(){return chapterDone(3);}},
  {id:'stars30', name:'Star Driver',      desc:'Collect 30 Journey stars.',                             test:function(){return journeyStars()>=30;}},
  {id:'journey', name:'Master of the Map',desc:'Complete all 15 Journey levels.',                       test:function(){return journeyDoneCount()>=LEVELS.length;}}
];
function checkAchievements(res,rp){
  var ctx={res:res,rp:rp,diff:G.diff,A:aggregate()},fresh=[];
  ACH.forEach(function(a){if(!S.ach[a.id]){var ok=false;try{ok=a.test(ctx);}catch(e){}if(ok)fresh.push(a);}});
  if(fresh.length)commit(function(s){fresh.forEach(function(a){if(!s.ach[a.id])s.ach[a.id]=Date.now();});});
  return fresh;
}
/* ---- recording a finished route (the only place results are written) ---- */
function recordResult(res){
  var info={pb:false,prevBest:0,firstClear:false,ach:[]};
  var mode=G.mode,diff=G.diff,lid=G.level?G.level.id:null,dk=G.dateKey,route=G.route.slice(),seed=G.seed,counted=G.counted;
  commit(function(s){
    delete s.drafts[mode];
    if(mode==='daily'){
      var prev=0,n=0;Object.keys(s.daily).forEach(function(k){prev=Math.max(prev,s.daily[k].eff);n++;});
      info.prevBest=prev;info.pb=n>0&&res.eff>prev;
      s.daily[dk]={seed:seed,diff:diff,path:route,dist:res.dist,opt:res.opt,eff:res.eff,points:res.points,turns:res.turns};
    }else if(mode==='journey'&&lid){
      var L=s.journey.levels[lid]||(s.journey.levels[lid]={done:false,best:0,pts:0,medal:0,tries:0,perfect:false});
      info.firstClear=!L.done;info.prevBest=L.best;info.pb=L.done&&res.eff>L.best;
      L.done=true;L.tries++;L.best=Math.max(L.best,res.eff);L.pts=Math.max(L.pts,res.points);L.medal=Math.max(L.medal,res.medal);if(res.perfect)L.perfect=true;
    }else if(counted){
      var p=s.practice;info.prevBest=p.bestEff;info.pb=p.completed>0&&res.eff>p.bestEff;
      p.completed++;p.totalEff+=res.eff;p.totalPoints+=res.points;p.bestEff=Math.max(p.bestEff,res.eff);p.bestScore=Math.max(p.bestScore,res.points);
      if(res.perfect)p.perfect++;p.byDiff[diff]++;
    }
  });
  info.ach=checkAchievements(res,rulesPresent(G.city));
  return info;
}
function submitRoute(){
  if(G.locked)return;
  var v=validateRoute(G.city,G.route);
  if(!v.ok){toast(v.msg,'error');Sound.play('error');return;}
  if(G.mode==='daily'){ /* another tab may have finished today's map while this one sat open */
    var d=readDisk();
    if(d&&d.daily[G.dateKey]&&validateRoute(G.city,d.daily[G.dateKey].path).ok){S=d;setupBoard();toast("Today's challenge was already finished in another tab. Showing that result.",'info');return;}
  }
  lockRoute(true);
}
function lockRoute(fresh){
  G.locked=true;G.drag=null;clearTimeout(G.draftT);G.draftT=0;
  var res=scoreRoute(G.city,G.route);G.result=res;G.leaks=analyseRoute(G.city,G.route);
  G.info=fresh?recordResult(res):null;
  if(G.mode!=='daily'&&!G.firstRes)G.firstRes=res;
  G.refs.hover.setAttribute('d','');svg.classList.add('locked');
  refresh(false);$('controlsWrap').hidden=true;
  if(fresh){
    Sound.play('submit');
    /* With motion reduced there is no reveal animation to time the reward to, so follow the confirmation directly. */
    if(res.perfect&&reduceMotion())setTimeout(function(){if(G.locked&&G.result===res)Sound.play('optimal');},330);
  }
  runReveal(fresh&&!reduceMotion(),fresh);
  if(fresh)focusMap(); /* the buttons that were just used are hidden; keep keyboard focus on the page */
}
/* ---- result insight: medal, plain-English explanation, detour markers, personal-best line ---- */
function medalSVG(tier){
  var m=MEDALS[tier];
  return '<svg class="medal-svg medal-'+m.key+'" viewBox="0 0 64 80" aria-hidden="true"><path class="rib" d="M14 0h13l9 27H23z"/><path class="rib r2" d="M50 0H37l-9 27h13z"/>'+
    '<circle class="m-disc" cx="32" cy="48" r="27"/><circle class="m-in" cx="32" cy="48" r="21"/>'+
    (tier===4?'<path class="m-star" d="M32 33l4.5 9.2 10.1 1.4-7.3 7.1 1.7 10.1-9-4.8-9 4.8 1.7-10.1-7.3-7.1 10.1-1.4z"/>':'<text class="m-num" x="32" y="55" text-anchor="middle">'+['✓','3','2','1'][tier]+'</text>')+'</svg>';
}
function explainText(res,top){
  var c=G.city,extra=res.extra,pct=extra/res.opt,out;
  if(res.perfect){out='You matched the optimal route. Every junction was the right call.';}
  else if(pct<=.02){out='So close. You finished just '+fmtM(extra)+' over the best route.'+(top.length===1?' One turn made the difference.':'');}
  else if(top.length===1){out='One junction made the difference: the road marked 1 added '+fmtM(top[0].leak)+'.';}
  else if(top.length>1){ /* markers are numbered in the order you drove them, so name the one that cost most */
    var big=0,rest=extra;top.forEach(function(t,i){if(t.leak>top[big].leak)big=i;rest-=t.leak;});
    out='You lost distance at '+top.length+' junctions, most at marker '+(big+1)+' ('+fmtM(top[big].leak)+' extra).'+(rest>0?' Smaller slips elsewhere added another '+fmtM(rest)+'.':'')+' At each red marker, a different turn would have been shorter.';}
  else out='You finished '+fmtM(extra)+' over the best route.';
  if(c.optimalFree&&c.optimal.dist>c.optimalFree.dist)out+=' Road rules made the best route '+fmtM(c.optimal.dist-c.optimalFree.dist)+' longer than the unrestricted shortest, so check closed roads and arrows before you commit.';
  if(!res.perfect&&res.eff<80)out+=' Every attempt teaches you the map. Try it again and beat this.';
  return out;
}
function pbText(res){
  var i=G.info,out=[],L=G.level;
  if(G.mode==='journey'&&L){
    out.push('Level goal: '+L.target+'% efficiency'+(res.eff>=L.target?' · reached':' · keep going')+'. Perfect needs the optimal route.');
    if(i&&i.pb)out.unshift('New personal best on this level (was '+i.prevBest.toFixed(1)+'%).');
    else if(i&&i.prevBest&&!i.firstClear)out.unshift('Your best on this level: '+i.prevBest.toFixed(1)+'%.');
  }else if(G.mode==='practice'&&!G.counted&&G.firstRes&&G.firstRes!==res){
    var dlt=res.eff-G.firstRes.eff;
    out.push(dlt>0?'Better than your first try by '+dlt.toFixed(1)+' points.':dlt<0?'Your first try was '+(-dlt).toFixed(1)+' points better.':'Matches your first try.');
  }else if(i&&i.pb){out.push(G.mode==='daily'?'A new best across your daily results.':'New personal best efficiency! (was '+i.prevBest.toFixed(1)+'%)');}
  else if(i&&i.prevBest){out.push('Your best '+(G.mode==='daily'?'daily':'practice')+' efficiency: '+i.prevBest.toFixed(1)+'%.');}
  return out.join(' ');
}
function drawDetours(top){
  var r=G.refs,N=G.city.nodes,h='';
  top.forEach(function(t,ix){var a=N[t.node],b=N[t.to];
    h+='<path class="dt-seg" d="M'+f(a.x)+' '+f(a.y)+'L'+f(b.x)+' '+f(b.y)+'"/>';});
  top.forEach(function(t,ix){var a=N[t.node];
    h+='<g class="dt" data-x="'+f(a.x)+'" data-y="'+f(a.y)+'"><circle r="10"/><text x="0" y="0.5">'+(ix+1)+'</text></g>';});
  r.det.innerHTML=h;applyScale(svg);
}
function confetti(){
  var host=$('fx');if(!host||reduceMotion())return;
  var cols=['var(--optimal)','var(--start)','var(--end)','var(--accent)','var(--route)'];host.textContent='';
  for(var i=0;i<44;i++){var s=document.createElement('span');s.className='cf';
    s.style.setProperty('--x',(Math.random()*100).toFixed(1)+'%');s.style.setProperty('--dx',((Math.random()-.5)*180).toFixed(0)+'px');
    s.style.setProperty('--r',(Math.random()*720-360).toFixed(0)+'deg');s.style.setProperty('--d',(1.5+Math.random()*1.1).toFixed(2)+'s');
    s.style.setProperty('--dl',(Math.random()*.4).toFixed(2)+'s');s.style.background=cols[i%cols.length];host.appendChild(s);}
  setTimeout(function(){host.textContent='';},3400);
}
function showInsight(res,animate,fresh,quiet){
  var leaks=G.leaks||[];
  var top=leaks.slice().sort(function(a,b){return b.leak-a.leak;}).slice(0,3).sort(function(a,b){return a.step-b.step;});
  $('resMedal').innerHTML=medalSVG(res.medal)+'<div class="medal-name"></div>';
  $('resMedal').querySelector('.medal-name').textContent=MEDALS[res.medal].name;
  $('resMedal').dataset.tier=res.medal;
  $('resExplain').textContent=explainText(res,top);
  var ch=$('resDetours');ch.textContent='';
  top.forEach(function(t,ix){var s=document.createElement('span');s.className='chip';var n=document.createElement('b');n.textContent=String(ix+1);s.append(n,' +'+fmtM(t.leak));ch.appendChild(s);});
  $('resPB').textContent=pbText(res);
  $('result').classList.toggle('perfect',res.perfect);$('mapFrame').classList.toggle('perfect',res.perfect);
  drawDetours(res.perfect?[]:top);
  if(quiet)return;
  announce('Result: '+res.eff.toFixed(1)+' percent efficiency, '+MEDALS[res.medal].name+' medal, '+res.points+' points. '+(res.extra?fmtM(res.extra)+' over the optimal route.':'You matched the optimal route.'));
  /* the reveal (and a replay of it) plays the medal moment; only the first showing of a result also reports new records and achievements */
  if(res.perfect){if(animate){Sound.play('optimal');confetti();}}
  else if(res.medal>=1&&(animate||fresh))Sound.play('medal',{tier:res.medal});
  if(!fresh)return;
  if(G.info&&G.info.pb&&!res.perfect)setTimeout(function(){Sound.play('pb');},res.medal>=1?520:0);
  var ac=G.info&&G.info.ach;
  if(ac&&ac.length)setTimeout(function(){toast('Achievement unlocked: '+ac.map(function(a){return a.name;}).join(', '),'good',4200);Sound.play('unlock');},res.perfect?1600:1100);
}
async function runReveal(animate,fresh){
  var tok=++G.anim,res=G.result,c=G.city,r=G.refs,box=$('result');
  var od=pathD(c.optimal.path);
  r.opt.setAttribute('d',od);r.optGlow.setAttribute('d',od);
  [r.opt,r.optGlow].forEach(function(p){p.style.strokeDasharray='1000';p.style.strokeDashoffset=animate?'1000':'0';});
  r.car.style.display='none';r.car2.style.display='none';r.det.innerHTML='';G.skip=null;
  box.hidden=false;box.dataset.stage='1';box.classList.remove('perfect');$('mapFrame').classList.remove('perfect');
  $('resEyebrow').textContent=G.review?'Completed':'Route locked';
  $('resLabel').textContent=animate?'Locked in':res.label;
  $('rlDist').textContent=fmtM(res.dist);$('rlTurns').textContent=res.turns;
  $('gaugeBox').innerHTML=gaugeHTML();
  $('retryBtn').hidden=G.mode==='daily';$('replayBtn').disabled=true;
  var notes=[];
  if(G.mode==='daily')notes.push(G.review?'Daily challenge completed. A fresh city arrives tomorrow.':'Daily result saved on this device. A fresh city arrives tomorrow.');
  else if(G.mode==='journey')notes.push('Journey progress saved. Your best result on each level is kept.');
  else if(!G.counted)notes.push('Practice retry. This attempt is not counted in your statistics.');
  else notes.push('Practice result saved.');
  if(!storageOK)notes.push('Storage is unavailable, so progress lasts only until you close this page.');
  $('resNote').textContent=notes.join(' ');
  $('nextBtn').textContent=G.mode==='daily'?'Try practice mode':G.mode==='journey'?(nextLevel()?'Next level':'Back to Journey'):'Next challenge';
  $('retryBtn').textContent=G.mode==='journey'?'Try this level again':'Try this map again';
  var finish=function(count,tk,quiet){
    tk=tk||tok;G.skip=null;
    box.dataset.stage='2';$('resEyebrow').textContent=G.review?'Completed':'Result';$('resLabel').textContent=res.label;
    $('replayBtn').disabled=false;
    var ms=count?900:0;
    countTo($('tDist'),res.dist,fmtM,ms,tk);countTo($('tOpt'),res.opt,fmtM,ms,tk);countTo($('tExtra'),res.extra,fmtM,ms,tk);
    countTo($('tEff'),res.eff,function(v){return v.toFixed(1)+'%';},ms,tk);
    countTo($('tPts'),res.points,function(v){return Math.round(v).toLocaleString('en-GB');},ms,tk);
    $('tTurns').textContent=res.turns;
    setGauge($('gaugeBox'),res.eff,count,res.eff.toFixed(1)+'%');
    showInsight(res,animate,fresh,quiet);
    if(document.activeElement===$('skipBtn'))$('replayBtn').focus();
  };
  if(!animate){[r.opt,r.optGlow].forEach(function(p){p.style.strokeDashoffset='0';});finish(false);return;}
  G.skip=function(quiet){ /* "Skip reveal": jump straight to the result (quietly when the player is leaving the page) */
    if(tok!==G.anim)return;var tk=++G.anim;
    r.car.style.display='none';r.car2.style.display='none';
    [r.opt,r.optGlow].forEach(function(p){p.style.strokeDashoffset='0';});finish(false,tk,quiet);
  };
  if(!await sleep(750,tok))return;
  /* The race: your car and the optimal car leave A together at the same speed. The optimal car arrives first, so the extra distance is something you can see. */
  var lenO=r.opt.getTotalLength(),lenP=r.glow.getTotalLength(),m=parseFloat(r.car.dataset.m||'1'),maxLen=Math.max(lenO,lenP,1);
  var angO=null,angP=null;
  function place(car,path,len,d,off,ang){
    var l=Math.min(d,len),a=path.getPointAtLength(l),b=path.getPointAtLength(Math.min(len,l+9));
    if(b.x===a.x&&b.y===a.y)b=path.getPointAtLength(Math.max(0,l-9)),b={x:2*a.x-b.x,y:2*a.y-b.y};
    var tgt=Math.atan2(b.y-a.y,b.x-a.x);
    if(ang===null)ang=tgt;else{var df=tgt-ang;while(df>Math.PI)df-=2*Math.PI;while(df<-Math.PI)df+=2*Math.PI;ang+=df*.32;}
    var ox=Math.sin(ang)*off*m,oy=-Math.cos(ang)*off*m;
    car.setAttribute('transform','translate('+(a.x+ox).toFixed(1)+' '+(a.y+oy).toFixed(1)+') rotate('+(ang*180/Math.PI).toFixed(1)+') scale('+(.92*m).toFixed(2)+')');
    return ang;
  }
  r.car.style.display='';r.car2.style.display='';
  var ok=await tween(clamp(maxLen*2.3,2000,4600),function(p){
    var e=p<.5?2*p*p:1-Math.pow(-2*p+2,2)/2,d=e*maxLen;
    angO=place(r.car,r.opt,lenO,d,-3.4,angO);angP=place(r.car2,r.glow,lenP,d,3.4,angP);
    var off=1000*(1-Math.min(1,d/lenO));r.opt.style.strokeDashoffset=off;r.optGlow.style.strokeDashoffset=off;
  },tok);
  if(!ok)return;
  r.opt.style.strokeDashoffset=0;r.optGlow.style.strokeDashoffset=0;
  await sleep(380,tok);
  if(tok!==G.anim)return;
  r.car.style.display='none';r.car2.style.display='none';
  finish(true);
  box.scrollIntoView({behavior:reduceMotion()?'auto':'smooth',block:'nearest'});
}
function shareText(){
  var r=G.result,label=G.mode==='daily'?'Daily '+G.dateKey:G.mode==='journey'&&G.level?'Journey '+G.level.id.replace('L','')+' '+G.level.title:'Practice';
  return 'THE WRONG WAY · '+label+' · '+DIFF_LABEL[G.diff].toUpperCase()+'\n'+['✔','🥉','🥈','🥇','⭐'][r.medal]+' '+MEDALS[r.medal].name+' · '+r.eff.toFixed(1)+'% efficiency · '+r.points+' pts\n'+fmtM(r.dist)+' driven vs '+fmtM(r.opt)+' optimal';
}
async function copyText(t){
  try{await navigator.clipboard.writeText(t);return true;}catch(e){}
  try{var ta=document.createElement('textarea');ta.value=t;ta.style.position='fixed';ta.style.opacity='0';document.body.appendChild(ta);ta.select();var ok=document.execCommand('copy');ta.remove();return ok;}catch(e2){return false;}
}

/* =====================================================================
   GAME SETUP
   ===================================================================== */
/* A map can't be built: practice quietly tries a neighbouring seed, then the classic generator. Daily and Journey never change their seed. */
function buildCity(){
  var attempts=G.mode==='practice'?3:1;
  for(var a=0;a<attempts;a++){
    try{
      if(G.mode==='daily'||(G.mode==='practice'&&G.rules==='classic'))return generateCity(G.seed,G.diff);
      return generateStrategic(G.seed,G.diff,G.mode==='journey'?G.level.spec:specFor(G.rules,G.diff));
    }catch(e){if(G.mode==='practice')G.seed=(G.seed+104729)>>>0;}
  }
  if(G.mode==='practice'){try{G.rules='classic';return generateCity(G.seed,G.diff);}catch(e2){}}
  return null;
}
function startGame(mode,opts){
  opts=opts||{};
  var prev={mode:G.mode,diff:G.diff,seed:G.seed,dateKey:G.dateKey,rules:G.rules,level:G.level,firstRes:G.firstRes};
  G.mode=mode;G.level=null;G.firstRes=null;
  if(mode==='daily'){G.dateKey=dateKey();G.diff=dailyDifficulty(G.dateKey);G.rules='classic';G.seed=hashString('wrongway:'+G.dateKey+':'+G.diff);}
  else if(mode==='journey'){G.level=levelById(opts.level);G.dateKey='';G.diff=G.level.diff;G.rules='journey';G.seed=levelSeed(G.level);}
  else{
    G.dateKey='';var dr=opts.resume?S.drafts.practice:null;
    if(dr){G.seed=dr.seed>>>0;G.diff=dr.diff;G.rules=dr.rules;}
    else{G.diff=opts.diff||S.settings.practiceDiff;G.rules=opts.rules||S.settings.rules;G.seed=(Date.now()^Math.floor(Math.random()*4294967296))>>>0;}
  }
  var city=buildCity();
  if(!city){ /* leave the previous game exactly as it was */
    G.mode=prev.mode;G.diff=prev.diff;G.seed=prev.seed;G.dateKey=prev.dateKey;G.rules=prev.rules;G.level=prev.level;G.firstRes=prev.firstRes;
    toast("Couldn't build that map. Please try again.",'error');announce("Couldn't build that map. Please try again.");return false;
  }
  G.city=city;setupBoard();return true;
}
function rulesKeyHTML(rp){
  var k=[];
  if(rp.river)k.push(['river','<svg viewBox="0 0 24 24"><path d="M2 8c4-4 6 4 10 0s6-4 10 0M2 15c4-4 6 4 10 0s6-4 10 0"/></svg>','River','cross only at bridges']);
  if(rp.works)k.push(['works','<svg viewBox="0 0 24 24"><path d="M4 8h16v6H4zM6 14v6M18 14v6M8 8l3 6M13 8l3 6"/></svg>','Roadworks','road closed']);
  if(rp.crash)k.push(['crash','<svg viewBox="0 0 24 24"><path d="M12 3l10 18H2zM12 10v5M12 18v.01"/></svg>','Accident','road closed']);
  if(rp.oneway)k.push(['oneway','<svg viewBox="0 0 24 24"><path d="M4 12h16M14 6l6 6-6 6"/></svg>','One-way','follow the arrows']);
  return k;
}
function renderRulesKey(){
  var box=$('rulesKey'),k=rulesKeyHTML(rulesPresent(G.city));box.textContent='';
  box.hidden=!k.length;
  k.forEach(function(it){var s=document.createElement('span');s.className='rk rk-'+it[0];s.innerHTML=it[1];var t=document.createElement('span');var b=document.createElement('b');b.textContent=it[2];t.append(b,' · '+it[3]);s.appendChild(t);box.appendChild(s);});
  /* the first time a rule appears, say what it means */
  var tips={works:'Orange barriers mean roadworks: that road is closed.',crash:'A red triangle marks an accident: that road is closed.',oneway:'Arrows on a road mean one-way: you can only drive in their direction.',river:'A river splits the city. You can only cross at the bridges.'};
  var rp=rulesPresent(G.city),first=['works','crash','oneway','river'].filter(function(n){return (n==='river'?rp.river:rp[n])&&!S.seen[n];});
  if(first.length){var msg=tips[first[0]];setTimeout(function(){if(G.view==='game'&&G.city)toast(msg,'info',5200);},650);
    commit(function(s){s.seen[first[0]]=true;});return true;} /* one tip per map; the next new rule gets its turn on a later map */
  return false;
}
function setupBoard(){
  var c=G.city;G.anim++;G.skip=null;
  buildMapSVG(svg,c,{buildings:S.settings.buildings});grabRefs();
  G.route=[c.start];G.locked=false;G.result=null;G.review=false;G.counted=true;G.leaks=null;G.info=null;
  svg.classList.remove('locked');$('result').hidden=true;$('controlsWrap').hidden=false;$('mapFrame').classList.remove('perfect');$('fx').textContent='';
  var isDaily=G.mode==='daily',isJourney=G.mode==='journey';
  $('gMode').textContent=isDaily?'Daily challenge':isJourney?'Journey · Chapter '+G.level.ch+' · '+CHAPTERS[G.level.ch-1].name:'Practice mode';
  $('gTitle').textContent=isDaily?prettyDate()+' · '+DIFF_LABEL[G.diff]:isJourney?'Level '+G.level.id.slice(1)+' · '+G.level.title:'Map #'+(G.seed%100000).toString().padStart(5,'0')+' · '+DIFF_LABEL[G.diff];
  var prac=G.mode==='practice';
  $('diffSeg').hidden=!prac;$('newMapBtn').hidden=!prac;$('rulesSel').hidden=!prac;
  syncDiffSeg();$('rulesSel').value=RULE_SETS[G.rules]?G.rules:'strategic';
  var badge=$('gBadge');badge.className='badge';badge.textContent='';
  if(isDaily){badge.textContent='One map per day';}
  else if(isJourney){var jr=S.journey.levels[G.level.id];badge.textContent='Goal '+G.level.target+'%'+(jr&&jr.done?' · Best '+jr.best.toFixed(1)+'%':'');}
  else badge.textContent='Unlimited attempts';
  G.u=applyScale(svg);
  var mf=$('mapFrame');mf.classList.remove('enter');void mf.offsetWidth;if(!reduceMotion())mf.classList.add('enter');
  refresh(false);
  var rec=isDaily?S.daily[G.dateKey]:null,tipShown=renderRulesKey();
  if(rec&&validateRoute(c,rec.path).ok){
    G.route=rec.path.slice();G.review=true;badge.textContent='Completed today';badge.classList.add('ok');
    lockRoute(false);
  }else{
    var dr=S.drafts[G.mode],mine=dr&&(isDaily?dr.key===G.dateKey:isJourney?dr.id===G.level.id:(dr.seed===G.seed&&dr.diff===G.diff&&dr.rules===G.rules));
    if(mine&&prac)G.counted=dr.counted!==false; /* a retry stays a retry, even if nothing has been drawn yet */
    if(mine&&validDraftRoute(c,dr.route)&&dr.route.length>1){
      G.route=dr.route.slice();refresh(false);
      toast('Welcome back. Your unfinished route has been restored.','good');
    }else if(!tipShown){
      toast(S.seen.firstDrive?'Click a ringed junction or drag along the streets from A to B.':'Click a ringed junction or drag along the streets from A to B. Every extra metre costs points.','info');
    }
    if(!G.counted){badge.className='badge warn';badge.textContent='Retry · not counted';}
    if(!S.seen.firstDrive)commit(function(s){s.seen.firstDrive=true;});
    if(prac)writeDraft();
  }
  Traffic.restart();
}
function syncDiffSeg(){var b=$('diffSeg').querySelectorAll('button');for(var i=0;i<b.length;i++)b[i].setAttribute('aria-pressed',String(b[i].dataset.diff===G.diff));}
async function retryMap(){
  G.counted=G.mode==='journey';G.anim++;G.skip=null;G.route=[G.city.start];G.locked=false;G.result=null;G.review=false;G.leaks=null;G.info=null;
  svg.classList.remove('locked');$('result').hidden=true;$('controlsWrap').hidden=false;$('mapFrame').classList.remove('perfect');$('fx').textContent='';
  G.refs.opt.setAttribute('d','');G.refs.optGlow.setAttribute('d','');G.refs.car.style.display='none';G.refs.car2.style.display='none';G.refs.det.innerHTML='';
  var badge=$('gBadge');
  if(G.mode==='journey'){var jr=S.journey.levels[G.level.id];badge.className='badge';badge.textContent='Goal '+G.level.target+'%'+(jr&&jr.done?' · Best '+jr.best.toFixed(1)+'%':'');}
  else{badge.className='badge warn';badge.textContent='Retry · not counted';}
  refresh(false);persistSoon();window.scrollTo({top:0,behavior:reduceMotion()?'auto':'smooth'});focusMap();
}
function levelUnlocked(L){var i=LEVELS.indexOf(L);if(i<=0)return true;var r=S.journey.levels[LEVELS[i-1].id];return !!(r&&r.done);}
function nextLevel(){if(G.mode!=='journey'||!G.level)return null;var i=LEVELS.indexOf(G.level);return LEVELS[i+1]||null;}
function nextChallenge(){
  if(G.mode==='daily'){navigate('practice');}
  else if(G.mode==='journey'){var n=nextLevel();if(n)navigate('journey',{level:n.id});else navigate('journey');}
  else{if(startGame('practice',{diff:G.diff,rules:G.rules==='classic'?'classic':S.settings.rules})){window.scrollTo({top:0,behavior:reduceMotion()?'auto':'smooth'});focusMap();}}
}
/* leaving a half-drawn route behind is the one action that deserves a question */
async function okToDiscard(what){
  if(G.locked||!G.city||G.route.length-1<3)return true;
  return confirmBox(what||'Start a new map?','Your drawn route will be lost.','Start new');
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
/* a saved daily result counts as perfect when its distance did not exceed the optimal one (same rule as scoring) */
function recPerfect(r){return r.opt>0&&r.dist>0?r.dist<=r.opt:r.eff>=100;}
function aggregate(){
  var ds=Object.keys(S.daily).map(function(k){return S.daily[k];}),pr=S.practice;
  var js=LEVELS.map(function(L){return S.journey.levels[L.id];}).filter(function(r){return r&&r.done;});
  var dCount=ds.length,pCount=pr.completed,jCount=js.length;
  var bestEff=Math.max(pr.bestEff,ds.reduce(function(m,r){return Math.max(m,r.eff);},0),js.reduce(function(m,r){return Math.max(m,r.best);},0));
  var bestScore=Math.max(pr.bestScore,ds.reduce(function(m,r){return Math.max(m,r.points);},0),js.reduce(function(m,r){return Math.max(m,r.pts);},0));
  var dEff=dCount?ds.reduce(function(s,r){return s+r.eff;},0)/dCount:0,pEff=pCount?pr.totalEff/pCount:0;
  var perfect=pr.perfect+ds.filter(recPerfect).length+js.filter(function(r){return r.perfect;}).length;
  var dPts=ds.reduce(function(s,r){return s+r.points;},0),jPts=js.reduce(function(s,r){return s+r.pts;},0);
  return {dCount:dCount,pCount:pCount,jCount:jCount,total:dCount+pCount+jCount,bestEff:bestEff,bestScore:bestScore,dEff:dEff,pEff:pEff,perfect:perfect,totalPts:dPts+pr.totalPoints+jPts,streak:computeStreak(),longest:longestStreak()};
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
    var em=document.createElement('div');em.className='empty';var b=document.createElement('b');b.textContent='No routes driven yet';em.append(b,'Finish a daily, practice or Journey challenge and your record will show up here.');
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
  /* Journey and achievements */
  var g5=document.createElement('div');g5.className='grid2';
  var cj=document.createElement('div');cj.className='card';var hj=document.createElement('div');hj.className='eyebrow';hj.textContent='Journey';cj.appendChild(hj);
  var stars=journeyStars(),tally=[0,0,0,0,0];LEVELS.forEach(function(L){var r=S.journey.levels[L.id];if(r&&r.done)tally[r.medal]++;});
  cj.append(barRow('Levels cleared',A.jCount+' of '+LEVELS.length,A.jCount/LEVELS.length*100,'g'),barRow('Stars',stars+' of '+LEVELS.length*3,stars/(LEVELS.length*3)*100,'y'));
  var mt=document.createElement('div');mt.className='medal-tally';
  for(var q=4;q>=1;q--){var sp=document.createElement('span');sp.innerHTML=medalSVG(q);var nn=document.createElement('b');nn.textContent='×'+tally[q];sp.appendChild(nn);sp.title=MEDALS[q].name;mt.appendChild(sp);}
  cj.appendChild(mt);
  var ca=document.createElement('div');ca.className='card';var ha=document.createElement('div');ha.className='eyebrow';
  var got=ACH.filter(function(a){return S.ach[a.id];}).length;ha.textContent='Achievements · '+got+' of '+ACH.length;ca.appendChild(ha);
  var ul=document.createElement('ul');ul.className='ach-list';
  ACH.forEach(function(a){var li=document.createElement('li');var on=!!S.ach[a.id];li.className=on?'on':'';
    var ic=document.createElement('span');ic.className='ach-ic';ic.setAttribute('aria-hidden','true');ic.textContent=on?'★':'🔒';
    var tx=document.createElement('span');var nm=document.createElement('b');nm.textContent=a.name;var ds2=document.createElement('small');ds2.textContent=a.desc;tx.append(nm,ds2);
    var st=document.createElement('span');st.className='sr-only';st.textContent=on?' (unlocked)':' (locked)';
    li.append(ic,tx,st);ul.appendChild(li);});
  ca.appendChild(ul);g5.append(cj,ca);body.appendChild(g5);
}
function firstOpenLevel(){for(var i=0;i<LEVELS.length;i++){var r=S.journey.levels[LEVELS[i].id];if(!r||!r.done)return LEVELS[i];}return null;}
function renderHome(){
  var A=aggregate();
  $('hsBest').textContent=A.bestEff?A.bestEff.toFixed(1)+'%':'—';$('hsDone').textContent=A.total;
  $('hsStreak').innerHTML='';$('hsStreak').append(String(A.streak));var sm=document.createElement('small');sm.textContent=A.streak===1?' day':' days';$('hsStreak').appendChild(sm);
  var gb=$('homeGauge');if(!gb.firstChild)gb.innerHTML=gaugeHTML();
  setGauge(gb,A.bestEff||0,false,A.bestEff?Math.round(A.bestEff)+'%':'—');
  var key=dateKey(),rec=S.daily[key],chip=$('dailyChip');
  chip.classList.toggle('done',!!rec);
  $('dailyChipText').textContent=prettyDate()+' · Daily · '+DIFF_LABEL[dailyDifficulty(key)]+(rec?' · Completed '+rec.eff.toFixed(1)+'%':' · Not played yet');
  var nx=firstOpenLevel(),jd=journeyDoneCount();
  $('journeyChip').classList.toggle('done',!nx);
  $('journeyChipText').textContent='Journey · '+jd+' of '+LEVELS.length+' levels'+(nx?' · next: '+nx.title:' · complete');
}
/* the Journey view: five chapters, three levels each, unlocked in order */
function mechTags(L){
  var sp=L.spec,t=[];
  if(sp.river)t.push('River');if(sp.closures)t.push('Roadworks');if(sp.oneway)t.push('One-way');
  return t;
}
function renderJourney(){
  var body=$('journeyBody');body.textContent='';
  var jd=journeyDoneCount(),stars=journeyStars(),nx=firstOpenLevel();
  var sum=document.createElement('div');sum.className='card j-sum';
  var l=document.createElement('div');var e1=document.createElement('div');e1.className='eyebrow';e1.textContent='Your progress';
  var big=document.createElement('div');big.className='j-big';big.textContent=jd+' / '+LEVELS.length+' levels · '+stars+' / '+LEVELS.length*3+' stars';
  l.append(e1,big,barRow('',' ',jd/LEVELS.length*100,'g'));
  var cont=document.createElement('button');cont.className='btn primary';cont.id='jContinue';
  cont.textContent=nx?(jd?'Continue · Level '+nx.id.slice(1):'Start Level 01'):'Replay a level';
  cont.disabled=!nx;cont.addEventListener('click',function(){if(nx)navigate('journey',{level:nx.id});});
  sum.append(l,cont);body.appendChild(sum);
  CHAPTERS.forEach(function(ch){
    var sec=document.createElement('section');sec.className='card j-ch';
    var head=document.createElement('div');head.className='j-head';
    var hh=document.createElement('div');var ey=document.createElement('div');ey.className='eyebrow';ey.textContent='Chapter '+ch.n;
    var h2=document.createElement('h2');h2.textContent=ch.name;var bl=document.createElement('p');bl.textContent=ch.blurb;hh.append(ey,h2,bl);head.appendChild(hh);
    sec.appendChild(head);
    var row=document.createElement('div');row.className='j-levels';
    LEVELS.filter(function(L){return L.ch===ch.n;}).forEach(function(L){
      var r=S.journey.levels[L.id],unl=levelUnlocked(L),st=levelStars(L);
      var b=document.createElement('button');b.type='button';b.className='j-lv'+(r&&r.done?' done':'')+(unl?'':' locked');b.dataset.id=L.id;b.dataset.snd='none';
      b.setAttribute('aria-disabled',String(!unl));
      var tags=mechTags(L).concat([DIFF_LABEL[L.diff]]);
      b.setAttribute('aria-label','Level '+L.id.slice(1)+', '+L.title+'. '+tags.join(', ')+'. Goal '+L.target+' percent. '+(unl?(r&&r.done?'Best '+r.best.toFixed(1)+' percent, '+MEDALS[r.medal].name+' medal, '+st+' of 3 stars.':'Not completed yet.'):'Locked. Finish the previous level first.'));
      var num=document.createElement('span');num.className='j-num';num.textContent=unl?L.id.slice(1):'🔒';num.setAttribute('aria-hidden','true');
      var mid=document.createElement('span');mid.className='j-mid';mid.setAttribute('aria-hidden','true');
      var tt=document.createElement('b');tt.textContent=L.title;var tg=document.createElement('small');tg.textContent=tags.join(' · ')+' · goal '+L.target+'%';mid.append(tt,tg);
      var rt=document.createElement('span');rt.className='j-right';rt.setAttribute('aria-hidden','true');
      if(r&&r.done){var md=document.createElement('span');md.className='j-medal';md.innerHTML=medalSVG(r.medal);var bs=document.createElement('small');bs.textContent=r.best.toFixed(1)+'%';rt.append(md,bs);}
      var sr=document.createElement('span');sr.className='j-stars';sr.setAttribute('aria-hidden','true');sr.textContent='★'.repeat(st)+'☆'.repeat(3-st);rt.appendChild(sr);
      b.append(num,mid,rt);
      b.addEventListener('click',function(){
        if(!unl){var prev=LEVELS[LEVELS.indexOf(L)-1];toast('Finish Level '+prev.id.slice(1)+' to unlock this one.','error');Sound.play('blocked');return;}
        Sound.play('tap');navigate('journey',{level:L.id});});
      row.appendChild(b);
    });
    sec.appendChild(row);body.appendChild(sec);
  });
}
function paintVol(){var r=$('volRange');r.style.setProperty('--p',r.value+'%');$('volOut').textContent=r.value+'%';r.setAttribute('aria-valuetext',r.value+' percent');}
function renderSettings(){
  var s=S.settings;
  [['themeSeg','theme','theme'],['setDiffSeg','diff','practiceDiff'],['motionSeg','motion','motion']].forEach(function(t){
    var bs=$(t[0]).querySelectorAll('button');for(var i=0;i<bs.length;i++)bs[i].setAttribute('aria-pressed',String(bs[i].dataset[t[1]]===s[t[2]]));});
  $('swHints').setAttribute('aria-checked',String(s.hints));$('swBuild').setAttribute('aria-checked',String(s.buildings));$('swTraffic').setAttribute('aria-checked',String(s.traffic));
  $('setRulesSel').value=s.rules;$('rulesNote').textContent=RULE_SETS[s.rules].note;
  $('swSound').setAttribute('aria-checked',String(s.sound&&Sound.supported));$('swSound').disabled=!Sound.supported;
  $('volRange').value=Math.round(s.volume*100);$('volRange').disabled=!(s.sound&&Sound.supported);paintVol();
  $('soundDesc').textContent=Sound.supported?'Short, quiet cues for drawing, undoing, blocked roads and results. Off until you turn it on.':'This browser has no Web Audio support, so sound is unavailable. The game plays the same without it.';
  $('storageNote').textContent=storageOK?'Progress is stored locally in this browser only.':'Local storage is unavailable. Your progress will last only until you close this page.';
}

/* =====================================================================
   AMBIENT TRAFFIC — a few small cars wandering the legal roads. Purely decorative.
   Off with reduced motion, when the tab is hidden, outside the game view, or if switched off in Settings.
   ===================================================================== */
var Traffic=(function(){
  var cars=[],raf=0,last=0,COLORS=['#8fa3bf','#c9a46a','#9d8fbf','#7fb59b','#bf8f8f','#a9b4c4'];
  function active(){return G.view==='game'&&!!G.city&&!!G.refs&&!!G.refs.traffic&&!document.hidden&&!reduceMotion()&&S.settings.traffic&&cars.length>0;}
  function spawn(car){ /* put a car on a random open road, facing a way it may legally drive */
    var es=G.city.edges.filter(function(e){return !e.closed;}),e=es[Math.floor(Math.random()*es.length)],from=e.ow!=null?e.ow:(Math.random()<.5?e.a:e.b);
    car.e=e;car.from=from;car.to=from===e.a?e.b:e.a;car.t=Math.random();car.ang=null;
  }
  function build(){
    stop();cars=[];var layer=G.refs&&G.refs.traffic;if(!layer)return;layer.textContent='';
    if(!G.city||reduceMotion()||!S.settings.traffic)return;
    var c=G.city,n=c.diff==='easy'?3:c.diff==='medium'?5:7,html='',i;
    if(!c.edges.some(function(e){return !e.closed;}))return;
    for(i=0;i<n;i++){var car={e:null,from:0,to:0,t:0,spd:22+Math.random()*16,ang:null,el:null};spawn(car);cars.push(car);html+=carHTML('tcar','','--cc:'+COLORS[i%COLORS.length]);}
    layer.innerHTML=html;
    for(i=0;i<cars.length;i++)cars[i].el=layer.children[i];
  }
  function nextEdge(car){
    var c=G.city,nb=c.adj[car.to].filter(function(q){return canGo(q.e,car.to);}),fwd=nb.filter(function(q){return q.to!==car.from;}),pool=fwd.length?fwd:nb;
    if(!pool.length)return false;
    var pick=pool[Math.floor(Math.random()*pool.length)];car.from=car.to;car.to=pick.to;car.e=pick.e;return true;
  }
  function step(dt){
    var N=G.city.nodes,k=clamp(G.u*.9,1,2)*.62;
    for(var i=0;i<cars.length;i++){
      var car=cars[i],len=car.e.len||1;
      car.t+=car.spd*G.u*dt/len;
      while(car.t>=1){car.t-=1;if(!nextEdge(car))spawn(car); /* a one-way dead end: reappear elsewhere instead of reversing */ len=car.e.len||1;}
      var A=N[car.from],B=N[car.to],dx=B.x-A.x,dy=B.y-A.y,l=Math.sqrt(dx*dx+dy*dy)||1,tgt=Math.atan2(dy,dx);
      if(car.ang===null)car.ang=tgt;else{var df=tgt-car.ang;while(df>Math.PI)df-=2*Math.PI;while(df<-Math.PI)df+=2*Math.PI;car.ang+=df*.22;}
      var off=2.1*G.u*.7; /* drive on the left */
      car.el.setAttribute('transform','translate('+(A.x+dx*car.t+dy/l*off).toFixed(1)+' '+(A.y+dy*car.t-dx/l*off).toFixed(1)+') rotate('+(car.ang*180/Math.PI).toFixed(1)+') scale('+k.toFixed(3)+')');
    }
  }
  function frame(ts){
    if(!active()){raf=0;return;}
    var dt=Math.min(.05,Math.max(0,(ts-last)/1000));last=ts;step(dt);raf=requestAnimationFrame(frame);
  }
  function start(){if(!raf&&active()){last=performance.now();raf=requestAnimationFrame(frame);}}
  function stop(){if(raf)cancelAnimationFrame(raf);raf=0;}
  return {restart:function(){build();start();},sync:function(){if(active())start();else stop();},stop:stop};
})();

/* =====================================================================
   NAVIGATION, DRAWER, MODAL
   ===================================================================== */
var PILL={home:'Home',daily:'Daily',practice:'Practice',journey:'Journey',stats:'Statistics',settings:'Settings',about:'About'};
var TITLES={home:'The Wrong Way | Can You Find the Best Route?',daily:'Daily Challenge | The Wrong Way',practice:'Practice | The Wrong Way',journey:'Journey | The Wrong Way',stats:'Statistics | The Wrong Way',settings:'Settings | The Wrong Way',about:'About | The Wrong Way'};
function isNav(h){return typeof h==='string'&&own(PILL,h);}
function showView(name){
  document.querySelectorAll('.view').forEach(function(v){v.hidden=v.id!=='view-'+name;});
  G.view=name;
}
/* polite screen-reader announcements (page changes, results, keyboard driving) */
function announce(msg){var el=$('srStatus');if(!el)return;el.textContent='';setTimeout(function(){el.textContent=msg;},60);}
function parseHash(){
  var h=(location.hash||'').replace(/^#/,'').split('/'),nav=isNav(h[0])?h[0]:'home';
  return {nav:nav,level:nav==='journey'&&h[1]&&levelById(h[1])?h[1]:null,valid:!location.hash||isNav(h[0])};
}
function pushHash(nav,lvl,opts){
  var h='#'+nav+(lvl?'/'+lvl:'');
  try{if(opts.history===false||location.hash===h)return;if(opts.replace)history.replaceState(null,'',h);else history.pushState(null,'',h);}catch(e){}
}
/* start a game with the game view already showing (so the map is measured at its real size); put the old view back if the map can't be built */
function enterGame(mode,o){var pv=G.view;showView('game');if(startGame(mode,o))return true;showView(pv);if(pv!=='game')toast("Couldn't build that map. Please try again.",'error');return false;}
function navigate(nav,opts){
  opts=opts||{};
  if(!isNav(nav))nav='home';
  if(!$('modal').hidden)closeModal(false);
  if(G.skip&&!(nav==='daily'||nav==='practice'||(nav==='journey'&&opts.level&&levelById(opts.level))))G.skip(true); /* leaving the map mid-reveal: settle it quietly (no sounds or toasts on the next page) */
  flushDraft();closeDrawer(true);
  var lvl=null;
  if(nav==='daily'){
    var fresh=G.mode==='daily'&&G.city&&G.dateKey===dateKey()&&!(!G.locked&&S.daily[G.dateKey]); /* reuse the board unless the result arrived from another tab */
    if(!fresh&&!enterGame('daily'))return false;
    showView('game');
  }else if(nav==='practice'){
    if((opts.fresh||!(G.mode==='practice'&&G.city))&&!enterGame('practice',{resume:!opts.fresh}))return false;
    showView('game');
  }else if(nav==='journey'){
    var L=opts.level?levelById(opts.level):null;
    if(L&&!levelUnlocked(L)){toast('Finish the previous level to unlock this one.','error');L=null;}
    if(L){
      if((opts.fresh||!(G.mode==='journey'&&G.level&&G.level.id===L.id&&G.city))&&!enterGame('journey',{level:L.id}))return false;
      lvl=L.id;showView('game');
    }else{showView('journey');renderJourney();}
  }else{showView(nav);if(nav==='stats')renderStats();if(nav==='home')renderHome();if(nav==='settings')renderSettings();}
  G.nav=nav;G.navLevel=lvl;$('modePill').textContent=PILL[nav]||'';
  document.title=TITLES[nav]||TITLES.home;
  document.querySelectorAll('.nav-item').forEach(function(b){if(b.dataset.nav===nav)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current');});
  pushHash(nav,lvl,opts);
  if(G.view==='game'){G.u=applyScale(svg);if(G.refs)refresh(false);}
  window.scrollTo(0,0);
  Traffic.sync();
  if(!opts.boot){try{$('main').focus({preventScroll:true});}catch(e){}announce((nav==='home'?'Home':TITLES[nav].split(' |')[0])+(lvl?', level '+lvl.slice(1):'')+' page');}
  return true;
}
/* Back / Forward and hand-edited hashes. An unknown hash is replaced with #home instead of leaving a blank page. */
function onHash(){
  var p=parseHash();
  if(!p.valid){try{history.replaceState(null,'','#home');}catch(e){}}
  if(p.nav===G.nav&&(p.level||null)===(G.navLevel||null))return;
  if(!navigate(p.nav,{level:p.level,history:false}))navigate('home',{history:false});
}
function openDrawer(){
  $('drawer').classList.add('open');$('drawer').setAttribute('aria-hidden','false');$('backdrop').classList.add('show');$('menuBtn').setAttribute('aria-expanded','true');
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
   KEYBOARD DRIVING — arrow keys move to the road that points that way, Backspace undoes, Enter submits at B
   ===================================================================== */
var COMPASS=['east','south-east','south','south-west','west','north-west','north','north-east'];
function compass(a,b){var ang=Math.atan2(b.y-a.y,b.x-a.x)*180/Math.PI;return COMPASS[((Math.round(ang/45)%8)+8)%8];}
function announceRoute(){
  var c=G.city,R=G.route,end=R[R.length-1],N=c.nodes;
  var opts=c.adj[end].filter(function(nb){return canGo(nb.e,end)&&R.indexOf(nb.to)<0;}).map(function(nb){return compass(N[end],N[nb.to]);});
  var msg=fmtM(routeDistance(c,R))+' driven. ';
  if(end===c.end)msg+='You are at B. Press Enter to submit.';
  else if(!opts.length)msg+='Dead end. Press Backspace to undo.';
  else msg+='Roads ahead: '+opts.join(', ')+'. B is to the '+compass(N[end],N[c.end])+'.';
  announce(msg);
}
function kbMove(dx,dy){
  if(G.locked)return;
  var c=G.city,R=G.route,end=R[R.length-1],N=c.nodes,best=-1,bs=.38,any=-1,as=.38;
  c.adj[end].forEach(function(nb){
    var vx=N[nb.to].x-N[end].x,vy=N[nb.to].y-N[end].y,l=Math.sqrt(vx*vx+vy*vy)||1,cs=(vx*dx+vy*dy)/l;
    if(cs>as){as=cs;any=nb.to;}
    if(cs>bs&&canGo(nb.e,end)&&R.indexOf(nb.to)<0){bs=cs;best=nb.to;}
  });
  if(best>=0){tryAdd(best,false);announceRoute();}
  else if(any>=0){var res=tryAdd(any,false);if(res==='back')announceRoute();else announce($('toast').textContent||'That road is not available.');}
  else{toast('No road leads that way from here.','error');Sound.play('error');announce('No road leads that way.');}
}

/* =====================================================================
   EVENT WIRING
   ===================================================================== */
function setSetting(k,v){commit(function(s){s.settings[k]=v;});}
/* the skip link would otherwise change the hash to #main, which the router treats as an unknown page */
$('skipLink').addEventListener('click',function(e){e.preventDefault();try{$('main').focus();}catch(x){}});
document.querySelectorAll('[data-nav]').forEach(function(el){el.addEventListener('click',function(e){e.preventDefault();navigate(el.dataset.nav);});});
$('menuBtn').addEventListener('click',openDrawer);$('closeBtn').addEventListener('click',function(){closeDrawer();});$('backdrop').addEventListener('click',function(){closeDrawer();});
$('settingsBtn').addEventListener('click',function(){navigate('settings');});
$('mOk').addEventListener('click',function(){closeModal(true);});$('mCancel').addEventListener('click',function(){closeModal(false);});
$('modal').addEventListener('pointerdown',function(e){if(e.target===$('modal'))closeModal(false);});
document.addEventListener('keydown',function(e){
  if(e.key==='Escape'){if(!$('modal').hidden){closeModal(false);return;}closeDrawer();return;}
  if((e.ctrlKey||e.metaKey)&&!e.shiftKey&&e.key.toLowerCase()==='z'&&G.view==='game'&&$('modal').hidden&&!$('drawer').classList.contains('open')){
    var t=e.target&&e.target.tagName;if(t==='INPUT'||t==='TEXTAREA'||t==='SELECT')return;e.preventDefault();undo();}
  if(e.key==='Tab'&&!$('modal').hidden){var els=$('modal').querySelectorAll('button'),first=els[0],last=els[els.length-1];
    if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}}
});
var KEYDIR={ArrowUp:[0,-1],ArrowDown:[0,1],ArrowLeft:[-1,0],ArrowRight:[1,0]};
svg.addEventListener('keydown',function(e){
  if(G.view!=='game'||!G.city||e.ctrlKey||e.metaKey||e.altKey)return;
  var d=KEYDIR[e.key];
  if(d){if(G.locked)return;e.preventDefault();kbMove(d[0],d[1]);}
  else if(e.key==='Backspace'||e.key==='Delete'){e.preventDefault();if(undo())announceRoute();}
  else if(e.key==='Enter'||e.key===' '){e.preventDefault();if(G.locked)return;if(G.route[G.route.length-1]===G.city.end)submitRoute();else announceRoute();}
});
svg.addEventListener('focus',function(){if(G.city&&!G.locked)announceRoute();});
$('startBtn').addEventListener('click',function(){navigate(S.daily[dateKey()]?'practice':'daily');});
$('practiceBtn').addEventListener('click',function(){var dr=S.drafts.practice;navigate('practice',{fresh:!(dr&&dr.route.length>1)});});
$('journeyBtn').addEventListener('click',function(){navigate('journey');});
$('journeyChip').addEventListener('click',function(){var nx=firstOpenLevel();navigate('journey',nx?{level:nx.id}:{});});
$('undoBtn').addEventListener('click',undo);$('clearBtn').addEventListener('click',clearRoute);$('resetBtn').addEventListener('click',resetBoard);$('submitBtn').addEventListener('click',submitRoute);
$('replayBtn').addEventListener('click',function(){if(G.locked)runReveal(!reduceMotion(),false);});
$('skipBtn').addEventListener('click',function(){if(G.skip)G.skip(false);});
$('retryBtn').addEventListener('click',retryMap);$('nextBtn').addEventListener('click',nextChallenge);
$('shareBtn').addEventListener('click',async function(){var ok=await copyText(shareText());toast(ok?'Result copied to clipboard.':'Could not copy. Select the numbers manually.',ok?'good':'error');Sound.play(ok?'confirm':'error');
  var b=$('shareBtn');if(ok){b.textContent='Copied!';setTimeout(function(){b.textContent='Copy result';},1600);}});
$('newMapBtn').addEventListener('click',async function(){if(!await okToDiscard('Start a new map?'))return;startGame('practice',{diff:G.diff});});
$('diffSeg').addEventListener('click',async function(e){var b=e.target.closest('button');if(!b)return;
  if(b.dataset.diff===G.diff&&G.route.length<=1&&!G.locked)return;
  if(!await okToDiscard('Change difficulty?'))return;
  setSetting('practiceDiff',b.dataset.diff);startGame('practice',{diff:b.dataset.diff});});
$('rulesSel').addEventListener('change',async function(){var sel=this,v=sel.value;
  if(!await okToDiscard('Change map rules?')){sel.value=G.rules;return;}
  setSetting('rules',v);startGame('practice',{diff:G.diff,rules:v});});
$('themeSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;setSetting('theme',b.dataset.theme);applyTheme();renderSettings();});
$('setDiffSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;setSetting('practiceDiff',b.dataset.diff);renderSettings();});
$('setRulesSel').addEventListener('change',function(){setSetting('rules',this.value);renderSettings();});
$('motionSeg').addEventListener('click',function(e){var b=e.target.closest('button');if(!b)return;setSetting('motion',b.dataset.motion);applyMotion();renderSettings();Traffic.restart();});
/* buttons that play their own, more specific sound opt out of the generic interface tick */
['undoBtn','clearBtn','resetBtn','submitBtn','shareBtn','mOk','wipeBtn'].forEach(function(id){$(id).dataset.snd='none';});
$('swSound').addEventListener('click',function(){
  var on=!S.settings.sound;setSetting('sound',on);renderSettings();
  if(on){Sound.unlock().then(function(ok){if(ok){Sound.setVolume();Sound.play('on');}});}
  else{Sound.play('off',{force:true});setTimeout(Sound.sync,400);} /* confirm blip, then release the audio device */
});
$('volRange').addEventListener('input',function(){
  S.settings.volume=Math.round(clamp(Number(this.value)/100,0,1)*100)/100;paintVol();Sound.setVolume();
});
$('volRange').addEventListener('change',function(){setSetting('volume',Math.round(clamp(Number(this.value)/100,0,1)*100)/100);Sound.play('tap');}); /* audible sample at the new level */
$('swHints').addEventListener('click',function(){setSetting('hints',!S.settings.hints);renderSettings();if(G.refs)refresh(false);});
$('swTraffic').addEventListener('click',function(){setSetting('traffic',!S.settings.traffic);renderSettings();Traffic.restart();});
$('swBuild').addEventListener('click',function(){setSetting('buildings',!S.settings.buildings);renderSettings();
  if(G.skip)G.skip(true);
  if(G.city){var keep=G.route.slice(),lk=G.locked,rv=G.review;buildMapSVG(svg,G.city,{buildings:S.settings.buildings});grabRefs();G.u=applyScale(svg);G.route=keep;
    if(lk&&G.result){svg.classList.add('locked');var od=pathD(G.city.optimal.path);G.refs.opt.setAttribute('d',od);G.refs.optGlow.setAttribute('d',od);
      [G.refs.opt,G.refs.optGlow].forEach(function(p){p.style.strokeDasharray='1000';p.style.strokeDashoffset=$('result').dataset.stage==='2'?'0':'1000';});
      if($('result').dataset.stage==='2'&&!G.result.perfect){var lk2=G.leaks||[];drawDetours(lk2.slice().sort(function(a,b){return b.leak-a.leak;}).slice(0,3).sort(function(a,b){return a.step-b.step;}));}}
    else svg.classList.remove('locked');refresh(false);Traffic.restart();}});
$('wipeBtn').addEventListener('click',async function(){
  var ok=await confirmBox('Reset all data?','This permanently deletes every daily result, practice statistic, Journey record, streak and setting stored in this browser.','Delete everything');
  if(!ok)return;
  Sound.play('clear'); /* played while sound is still on; the audio device is released a moment later so the cue is actually heard */
  S=defaults();save();applyTheme();applyMotion();setTimeout(Sound.sync,450);renderSettings();Traffic.stop();
  G.anim++;G.skip=null;G.locked=false;G.result=null;G.route=[];G.city=null;G.mode='daily';G.refs=null;G.level=null;G.info=null;G.leaks=null;toast('All data reset.','info');
});

var rsT=0;
function onResize(){clearTimeout(rsT);rsT=setTimeout(function(){
  if(G.city&&G.refs&&G.view==='game'){G.u=applyScale(svg);refresh(false);}
  var pv=$('previewSvg');if(pv.firstChild&&G.view==='home')applyScale(pv);
},60);}
if(window.ResizeObserver){new ResizeObserver(onResize).observe($('mapFrame'));new ResizeObserver(onResize).observe(document.querySelector('.preview'));}
window.addEventListener('resize',onResize);
if(window.matchMedia){try{matchMedia('(prefers-reduced-motion: reduce)').addEventListener('change',function(){applyMotion();Traffic.restart();});}catch(e){}}
window.addEventListener('hashchange',onHash);window.addEventListener('popstate',onHash);
document.addEventListener('visibilitychange',function(){if(document.hidden)flushDraft();Traffic.sync();});
window.addEventListener('pagehide',flushDraft);
/* another tab changed the saved data: adopt it, so this tab can never overwrite it with older state */
window.addEventListener('storage',function(e){
  if(e.key!==null&&e.key!==STORE_KEY)return;
  S=readDisk()||defaults();
  applyTheme();applyMotion();Sound.sync();
  if(G.view==='settings')renderSettings();else if(G.view==='stats')renderStats();else if(G.view==='home')renderHome();else if(G.view==='journey')renderJourney();
  if(G.view==='game'&&G.mode==='daily'&&G.city&&!G.locked){var rec=S.daily[G.dateKey];
    if(rec&&validateRoute(G.city,rec.path).ok){setupBoard();toast("Today's challenge was finished in another tab. Showing that result.",'info');}}
});

/* =====================================================================
   BOOT
   ===================================================================== */
function renderPreview(){
  var pv=$('previewSvg'),seed=(Date.now()^0x5bd1e995)>>>0,city;
  try{city=generateStrategic(seed,'medium',{tier:2,river:3,riverP:1,closures:1,oneway:1});}catch(e){city=generateCity(seed,'medium');}
  buildMapSVG(pv,city,{buildings:true});
  var od=pathD2(city,city.optimal.path),o=pv.querySelector('.opt'),og=pv.querySelector('.opt-glow');
  o.setAttribute('d',od);og.setAttribute('d',od);o.classList.add('preview-anim');og.classList.add('preview-anim');
  applyScale(pv);
}
function pathD2(city,ids){return 'M'+ids.map(function(i){return f(city.nodes[i].x)+' '+f(city.nodes[i].y);}).join('L');}
applyTheme();applyMotion();
(function boot(){
  try{renderPreview();}catch(e){}
  var p=parseHash();
  if(!p.valid){try{history.replaceState(null,'','#home');}catch(e){}}
  if(!navigate(p.nav,{level:p.level,boot:true,replace:true}))navigate('home',{boot:true,replace:true});
})();
})();
});
