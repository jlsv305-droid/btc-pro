/* ============================================================================
   app.js — UI layer. Needs engine.js loaded first.
   No inline onclick handlers anywhere (MV3 CSP-safe): one delegated click
   listener reads data-act attributes.
   ============================================================================ */

const $=s=>document.querySelector(s);
const fmt=n=>"$"+Math.round(n).toLocaleString("en-US");
const fmtRange=(a,b)=>fmt(Math.min(a,b))+" – "+fmt(Math.max(a,b));
const sentColor=v=>v<25?"#ff1744":v<45?"#ff8a80":v<55?"#ffb300":v<75?"#69f0ae":"#00e676";
const LABELS=["12H","1D","3D","1W"];
const ASSETS=[['BTC','bitcoin'],['ETH','ethereum']];
let sel=1, store={}, sentiment=null, asset='BTC', minerCost=null, changeLog=null;
let rangeKey='1Y', chartBig=false, botState=null, botBusy=false, botJournalAll=false;
let chartHidden=(typeof window!=='undefined' && window.innerWidth<760);

function ladderUp(p,levels,atr){let cands=[...levels];[1.5,3,4.5,6].forEach(m=>cands.push(p+m*atr));
  cands=cands.filter(x=>x>p*1.004).sort((a,b)=>a-b);const out=[];
  for(const v of cands){if(out.length>=3)break;if(!out.some(x=>Math.abs(x-v)/x<0.015))out.push(v);}
  let l=out.length?out[out.length-1]:p;while(out.length<3){l+=1.5*atr;out.push(l);}return out.slice(0,3);}
function ladderDown(p,levels,atr){let cands=[...levels];[1.5,3,4.5,6].forEach(m=>cands.push(p-m*atr));
  cands=cands.filter(x=>x<p*0.996&&x>0).sort((a,b)=>b-a);const out=[];
  for(const v of cands){if(out.length>=3)break;if(!out.some(x=>Math.abs(x-v)/x<0.015))out.push(v);}
  let l=out.length?out[out.length-1]:p;while(out.length<3){l=Math.max(l-1.5*atr,1);out.push(l);}return out.slice(0,3);}
function buildPlan(cur){
  const p=cur.price, atr=p*cur.atrPct/100;
  const sup=cur.levels.sup, res=cur.levels.res;
  const buyC = sup.length?sup[0]:p-1.5*atr;
  const buyStop = sup.length>1?Math.min(sup[1],buyC-1.2*atr):buyC-1.2*atr;
  const buyTgts = ladderUp(p,res,atr);
  const sellC = res.length?res[0]:p+1.5*atr;
  const sellStop = res.length>1?Math.max(res[1],sellC+1.2*atr):sellC+1.2*atr;
  const sellTgts = ladderDown(p,sup,atr);
  return {p,atr,buyC,buyStop,buyTgts,sellC,sellStop,sellTgts};
}

/* market regime & whale flow read the DAILY series (store[1]) */
function marketRegime(){
  const c=store[1].c, i=c.length-1, p=c[i];
  const e200=ema(c,200), e50=ema(c,50);
  if(e200[i]!=null){
    const slope=e200[i]-e200[i-10], above=p>e200[i];
    if(above&&slope>0)return{t:"BULL MARKET",c:"#00e676",note:"Price is above the rising 200-day average"};
    if(!above&&slope<0)return{t:"DOWNTREND",c:"#ff1744",note:"Price is below the falling 200-day average"};
    return{t:"NEUTRAL / TRANSITION",c:"#ffb300",note:above?"Above the 200-day average, but it's flattening":"Below the 200-day average, but stabilizing"};
  }
  return p>e50[i]?{t:"BULLISH",c:"#00e676",note:"Price above the 50-day average"}:{t:"DOWNTREND",c:"#ff1744",note:"Price below the 50-day average"};
}
function whaleActivity(){
  const c=store[1].c, v=store[1].v, i=c.length-1;
  const ob=obv(c,v), back=Math.min(14,i), slope=ob[i]-ob[i-back];
  const obAbs=Math.max(...ob.map(Math.abs))||1, n=slope/obAbs;
  let volAvg=0,cnt=0;for(let k=Math.max(0,i-20);k<=i;k++){volAvg+=v[k];cnt++;}volAvg/=cnt;
  let spikes=0;for(let k=Math.max(0,i-9);k<=i;k++)if(v[k]>volAvg*1.6)spikes++;
  if(n>0.06)return{t:"Accumulating",c:"#00e676",note:"On-balance volume is rising — large buyers stepping in",spikes};
  if(n<-0.06)return{t:"Distributing",c:"#ff1744",note:"On-balance volume is falling — large holders selling",spikes};
  return{t:"Neutral",c:"#ffb300",note:"No clear large-player bias right now",spikes};
}

/* ============================ CHART ============================ */
let chartState={full:[],plan:null,markers:[],view:{a:0,b:0},hover:-1};
function drawChart(cv,fullData,plan,allMarkers,view){
  const a=view?Math.max(0,view.a):0, b=view?Math.min(fullData.length,view.b):fullData.length;
  const data=fullData.slice(a,b); if(data.length<2)return;
  const dpr=window.devicePixelRatio||1,w=cv.clientWidth,H=chartBig?Math.max(300,Math.round((window.innerHeight||700)*0.66)):(w>=820?340:220);
  cv.width=w*dpr;cv.height=H*dpr;
  const ctx=cv.getContext("2d");ctx.scale(dpr,dpr);ctx.clearRect(0,0,w,H);
  const pad=10;
  const vals=[];data.forEach(d=>{[d.h,d.l,d.o,d.price,d.st].forEach(v=>{if(v!=null)vals.push(v);});});
  const min=Math.min(...vals),max=Math.max(...vals);
  const X=i=>pad+(i/(data.length-1))*(w-2*pad);
  const Y=v=>pad+(1-(v-min)/((max-min)||1))*(H-2*pad);
  chartState._geo={a,w,pad,n:data.length};
  ctx.lineWidth=1.3;
  for(let i=1;i<data.length;i++){if(data[i].st==null||data[i-1].st==null)continue;
    ctx.beginPath();ctx.moveTo(X(i-1),Y(data[i-1].st));ctx.lineTo(X(i),Y(data[i].st));
    ctx.strokeStyle=data[i].stDir===1?"rgba(0,230,118,.35)":"rgba(255,23,68,.35)";ctx.stroke();}
  const bw=(w-2*pad)/data.length, dense=bw<2.4, body=Math.max(1.5,Math.min(bw*0.62,9));
  data.forEach((d,i)=>{const x=X(i),o=d.o!=null?d.o:d.price,cl=d.price,up=cl>=o,col=up?"#00e676":"#ff1744";
    const hi=d.h!=null?Math.max(d.h,o,cl):Math.max(o,cl), lo=d.l!=null?Math.min(d.l,o,cl):Math.min(o,cl);
    ctx.strokeStyle=col;ctx.fillStyle=col;ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(x,Y(hi));ctx.lineTo(x,Y(lo));ctx.stroke();
    if(!dense){const y1=Y(o),y2=Y(cl),top=Math.min(y1,y2),hgt=Math.max(1.5,Math.abs(y1-y2));
    ctx.fillRect(x-body/2,top,body,hgt);}});
  (allMarkers||[]).forEach(m=>{const gi=m.ci-a; if(gi<0||gi>=data.length)return; const d=data[gi];const x=X(gi);
    if(m.type==='buy'){const y=Y(d.l!=null?Math.min(d.l,d.o,d.price):Math.min(d.o,d.price))+9;
      ctx.fillStyle="#00e676";ctx.beginPath();ctx.moveTo(x,y);ctx.lineTo(x-5,y+8);ctx.lineTo(x+5,y+8);ctx.closePath();ctx.fill();}
    else{const y=Y(d.h!=null?Math.max(d.h,d.o,d.price):Math.max(d.o,d.price))-9;
      ctx.fillStyle="#ff1744";ctx.beginPath();ctx.moveTo(x,y);ctx.lineTo(x-5,y-8);ctx.lineTo(x+5,y-8);ctx.closePath();ctx.fill();}});
  const hv=chartState.hover;
  if(hv>=a&&hv<b){const gi=hv-a,x=X(gi),d=data[gi];
    ctx.setLineDash([3,3]);ctx.strokeStyle="rgba(220,225,220,.45)";ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(x,pad);ctx.lineTo(x,H-pad);ctx.stroke();
    ctx.beginPath();ctx.moveTo(pad,Y(d.price));ctx.lineTo(w-pad,Y(d.price));ctx.stroke();ctx.setLineDash([]);
    ctx.fillStyle="#cfd3cf";ctx.beginPath();ctx.arc(x,Y(d.price),2.5,0,7);ctx.fill();}
}
function fmtBar(d){const date=new Date(d.t).toLocaleDateString(undefined,{year:'numeric',month:'short',day:'numeric'});
  return `<b>${date}</b> &nbsp; O ${fmt(d.o)} · H ${fmt(d.h)} · L ${fmt(d.l)} · <b style="color:#cfd3cf">C ${fmt(d.price)}</b>`;}
function drawNow(){const cv=$("#cv");if(cv&&chartState.full.length)drawChart(cv,chartState.full,chartState.plan,chartState.markers,chartState.view);}
function hoverAt(clientX,cv){const g=chartState._geo;if(!g)return;const rect=cv.getBoundingClientRect();
  const rel=Math.max(0,Math.min(1,(clientX-rect.left-g.pad)/(g.w-2*g.pad)));
  const gi=Math.round(rel*(g.n-1)), idx=g.a+gi; chartState.hover=idx;
  const d=chartState.full[idx]; const info=document.getElementById("cvInfo");
  if(d&&info)info.innerHTML=fmtBar(d); drawNow();}
function setupChart(){
  const cv=$("#cv"); if(!cv)return;
  const card=document.querySelector(".chartCard"); if(card)card.classList.toggle("big",chartBig);
  drawNow();
  const pad=10; const wOf=()=>cv.clientWidth;
  cv.onwheel=(e)=>{e.preventDefault();const v=chartState.view,full=chartState.full.length,span=v.b-v.a,w=wOf();
    const mx=Math.max(0,Math.min(1,(e.offsetX-pad)/(w-2*pad))),center=v.a+mx*span;
    let ns=Math.round(span*(e.deltaY>0?1.25:0.8));ns=Math.max(20,Math.min(full,ns));
    let na=Math.round(center-mx*ns);na=Math.max(0,Math.min(full-ns,na));v.a=na;v.b=na+ns;drawNow();};
  let drag=null;
  cv.onmousedown=(e)=>{drag={x:e.clientX,a:chartState.view.a,moved:false};};
  window.onmousemove=(e)=>{ if(drag){const v=chartState.view,full=chartState.full.length,span=v.b-v.a,w=wOf();
      if(Math.abs(e.clientX-drag.x)>3)drag.moved=true;
      const shift=Math.round(-(e.clientX-drag.x)/(w-2*pad)*span);
      let na=Math.max(0,Math.min(full-span,drag.a+shift));v.a=na;v.b=na+span;drawNow();return;}
    if(cv._inside)hoverAt(e.clientX,cv); };
  window.onmouseup=()=>{drag=null;};
  cv.onmouseenter=()=>{cv._inside=true;};
  cv.onmousemove=(e)=>{if(!drag)hoverAt(e.clientX,cv);};
  cv.onmouseleave=()=>{cv._inside=false;chartState.hover=-1;const info=document.getElementById("cvInfo");if(info)info.innerHTML="Hover a candle to see its date &amp; price · scroll to zoom · drag to pan";drawNow();};
  cv.ontouchstart=(e)=>{if(e.touches.length===1){drag={x:e.touches[0].clientX,a:chartState.view.a};hoverAt(e.touches[0].clientX,cv);}};
  cv.ontouchmove=(e)=>{if(!drag||e.touches.length!==1)return;const v=chartState.view,full=chartState.full.length,span=v.b-v.a,w=wOf();
    const shift=Math.round(-(e.touches[0].clientX-drag.x)/(w-2*pad)*span);
    let na=Math.max(0,Math.min(full-span,drag.a+shift));v.a=na;v.b=na+span;drawNow();};
  cv.ontouchend=()=>{drag=null;};
}

/* ============================ BOT CARD (v4) ============================ */
function drawBotEq(){
  const cv=document.getElementById('botEq'); if(!cv||!botState)return;
  const st=botState;
  const hist=(st.eqHist||[]).map(x=>x[1]);
  const eq=[st.startEquity||100000].concat(hist.length?hist:st.trades.filter(t=>!t.localManual).map(t=>t.eqAfter));
  eq.push(botMtm(st).equity);
  if(eq.length<2)return;
  const dpr=window.devicePixelRatio||1,w=cv.clientWidth||300,H=46;
  cv.width=w*dpr;cv.height=H*dpr;const ctx=cv.getContext('2d');ctx.scale(dpr,dpr);
  const mn=Math.min(...eq),mx=Math.max(...eq);
  const X=i=>i/(eq.length-1)*(w-4)+2, Y=v=>4+(1-(v-mn)/((mx-mn)||1))*(H-8);
  ctx.beginPath();eq.forEach((v,i)=>{i?ctx.lineTo(X(i),Y(v)):ctx.moveTo(X(i),Y(v));});
  ctx.strokeStyle=eq[eq.length-1]>=eq[0]?'#00e676':'#ff1744';ctx.lineWidth=1.6;ctx.stroke();
}
function renderBot(curPrice){
  if(!botState)return `<div class="secTitle">🤖 BTC PRO BOT · paper trading</div><div class="paper"><div class="paperEmpty">Starting up the bot…</div></div>`;
  const st=botState, scan=st.lastScan, cloud=botCloudFresh(st);
  const brain=(typeof BOT_HAS_BRAIN!=='undefined'&&BOT_HAS_BRAIN);
  const startEq=st.startEquity||100000, netDep=st.netDeposits||0;
  const pxOf=sym=>(sym===asset&&curPrice)?curPrice:(st.lastPx&&st.lastPx[sym])||null;
  const money=v=>(v<0?'−$':'+$')+Math.abs(v).toLocaleString('en-US',{maximumFractionDigits:Math.abs(v)<100?2:0});
  const pnlCol=v=>v>0.005?'#00e676':v<-0.005?'#ff1744':'#ffb300';
  const fmtD=t=>new Date(t).toLocaleDateString(undefined,{month:'short',day:'numeric'});
  const nameOf=id=>(BOT_SETUPS.find(s=>s[0]===id)||[0,'—'])[1];
  const live=(st.positions||[]).map(o=>{const px=pxOf(o.sym)||o.entry;return Object.assign({o,px},botPosPnl(st,o,px));});
  const botPos=live.filter(x=>x.o.setup!=='manual').sort((a,b)=>a.o.setup===b.o.setup?b.usd-a.usd:(a.o.setup<b.o.setup?-1:1));
  const manPos=live.filter(x=>x.o.setup==='manual');
  const unreal=botPos.reduce((a,x)=>a+x.usd,0);
  const realized=st.equity-startEq-netDep;
  const totalPnl=realized+unreal, totalPct=totalPnl/(startEq+Math.max(0,netDep))*100;
  const eqNow=st.equity+unreal;
  const invested=botPos.reduce((a,x)=>a+x.o.usd+x.usd,0), invPct=eqNow>0?Math.max(0,Math.min(100,invested/eqNow*100)):0;
  const all=(st.trades||[]).slice().sort((a,b)=>(a.exitT||0)-(b.exitT||0));
  const tr=all.filter(t=>!t.localManual);
  const sleeves=BOT_SETUPS.filter(x=>x[0]!=='manual').map(([id,nm])=>Object.assign({id,nm},{hits:0,total:0,usd:0},(st.setups||{})[id]||{}));
  const closedN=Math.max(tr.length,sleeves.reduce((a,s)=>a+(s.total||0),0));
  const winsN=Math.max(tr.filter(t=>t.usd>0).length,sleeves.reduce((a,s)=>a+(s.hits||0),0));
  const winRate=closedN?Math.round(winsN/closedN*100):null;
  const gw=tr.filter(t=>t.usd>0).reduce((a,t)=>a+t.usd,0), gl=Math.abs(tr.filter(t=>t.usd<=0).reduce((a,t)=>a+t.usd,0));
  const pf=tr.length?(gl>0?(gw/gl):(gw>0?Infinity:null)):null;
  const best=tr.length?Math.max(...tr.map(t=>t.usd)):null, worst=tr.length?Math.min(...tr.map(t=>t.usd)):null;
  const holdRet=(st.startPrice&&pxOf('BTC'))?((pxOf('BTC')/st.startPrice-1)*100):null;
  const nTrades=closedN+botPos.length;
  const weeks=(Date.now()-(st.createdAt||Date.now()))/(7*86400000);
  const perWeek=weeks>=1?nTrades/weeks:null;
  const nr=botNextRun(new Date());
  const nrTxt=nr.toLocaleDateString(undefined,{weekday:'short'})+' '+nr.toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});

  /* open positions: one compact row each, tap for details */
  const posHtml=botPos.map(x=>{const o=x.o,c=pnlCol(x.usd);
    const days=Math.max(0,Math.floor((Date.now()-o.entryT)/86400000));
    return `<div class="trade"><div class="trHead" data-act="tg" data-id="bp${o.id}">
      <span><b style="color:#9ff0c4">${o.sym}</b> <small style="color:#7d827d">${nameOf(o.setup)} · ${fmt(o.usd)} · ${days}d</small></span>
      <b style="color:${c}">${money(x.usd)} <small style="font-weight:600">${x.pct>=0?'+':''}${x.pct.toFixed(1)}%</small></b></div>
      <div id="bp${o.id}" class="trDet">
        <div class="trd"><span>Bought</span><b>${botPx(o.entry)} · ${fmtD(o.entryT)}</b></div>
        <div class="trd"><span>Price now</span><b>${botPx(x.px)}</b></div>
        <div class="trd"><span>Amount</span><b>${fmt(o.usd)} · ${o.sizePct}% of the account</b></div>
        <div class="trd"><span>It will be sold when</span><b style="text-align:right">${o.setup==='rot'?'it leaves the strongest group, or the market filter turns off':'its trend weakens'}</b></div>
        ${cloud?'':`<button class="logBtn ghost" data-act="botclose" data-id="${o.id}" style="width:100%;margin-top:8px">✕ Close this trade now</button>`}
      </div></div>`;}).join('');

  /* your manual trades (device-local, separate from the bot's record) */
  const manHtml=manPos.map(x=>{const o=x.o,isL=o.dir===1,pc=x.pct>=0?'#00e676':'#ff1744';
    return `<div class="pos" style="border-color:${pc};margin-top:10px">
      <div class="posTop"><span class="posState" style="color:${isL?'#00e676':'#ff7eb6'}">● ${o.sym} ${isL?'LONG':'SHORT'} · MANUAL · ${o.sizePct}%${o.scaled?' · <small style="color:#69f0ae">50% banked ✓</small>':''}</span>
        <span class="posPnl" style="color:${pc}">${money(x.usd)} <small style="font-weight:600">${x.pct>=0?'+':''}${x.pct.toFixed(1)}%</small></span></div>
      <div class="posGrid">
        <div><span>Opened</span><b>${o.date}</b></div>
        <div><span>Entry</span><b>${botPx(o.entry)}</b></div>
        <div><span>${o.scaled?'Trailing stop':'Stop loss'}</span><b style="color:${o.scaled?'#ffd54f':'#ff8a80'}">${botPx(o.stop)}</b></div>
        ${o.scaled?`<div><span>Final target</span><b style="color:#69f0ae">${botPx(o.t2)}</b></div>`
                  :`<div><span>Target 1 (take 50%)</span><b style="color:#69f0ae">${botPx(o.t1)}</b></div>
        <div><span>Final target</span><b style="color:#69f0ae">${botPx(o.t2)}</b></div>`}
      </div>
      <button class="logBtn ghost" data-act="botclose" data-id="${o.id}" style="width:100%;margin-top:9px">✕ Close this trade now</button>
    </div>`;}).join('');

  const sleeveHtml=sleeves.map(s=>{const open=botPos.filter(x=>x.o.setup===s.id).length;
    return `<span class="bdChip"><i style="background:${s.usd>0?'#00e676':s.usd<0?'#ff5c7a':'#7d827d'}"></i>${s.nm} <b>${s.hits}/${s.total} won</b> <small style="color:#7d827d">${s.total?money(s.usd)+' · ':''}${open} open</small></span>`;}).join('');

  const news=st.news;
  const newsHtml=news?`<div class="ensBd"><div class="ensBdTitle">📰 News radar — ${news.n} headlines, last 36h <span class="ig" data-act="tip" data-tip="Titulares de CoinDesk, Cointelegraph y Decrypt puntuados por palabras clave. Es solo informativo: el bot v4 NO opera por noticias — en las pruebas, operar por titulares no dio ventaja. Decide solo con precios.">ⓘ</span></div>
    <div class="ensStats">Sentiment: <b style="color:${news.sent>=0.25?'#00e676':news.sent<=-0.25?'#ff5c7a':'#ffb300'}">${news.sent>=0.25?'bullish':news.sent<=-0.25?'bearish':'neutral'} (${news.sent>=0?'+':''}${news.sent})</b> · Event risk: <b style="color:${news.vol>=0.6?'#ff8a80':news.vol>=0.3?'#ffb300':'#69f0ae'}">${news.vol>=0.6?'high':news.vol>=0.3?'medium':'low'}</b> <small style="color:#7d827d">· information only</small></div>
    ${(news.top||[]).map(x=>`<div class="trd"><span style="flex:1;line-height:1.35">${x.t}</span><b style="white-space:nowrap;margin-left:8px;color:${x.sent>0?'#69f0ae':x.sent<0?'#ff8a80':'#ffb300'}">${x.sent>0?'▲':x.sent<0?'▼':'•'}${x.vol>=1.5?' ⚡':''} <small style="color:#5f6b5f">${x.src}</small></b></div>`).join('')}
  </div>`:'';
  const activity=(st.activity||[]).slice(-30).reverse().map(a=>{
    const col=a.kind==='win'?'#69f0ae':a.kind==='loss'?'#ff8a80':a.kind==='open'?'#7fb2e0':'#9aa09a';
    const d=new Date(a.ts);
    const ds=d.toLocaleDateString(undefined,{month:'short',day:'numeric'})+' '+d.toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
    return `<div class="trd"><span style="white-space:nowrap">${ds}</span><b style="color:${col};text-align:right;margin-left:10px">${a.txt}</b></div>`;}).join('');

  const showN=botJournalAll?all.length:12;
  const jrows=all.slice(-showN).reverse().map((t,k)=>{const id="bj"+k,c=t.usd>=0?"#00e676":"#ff1744";
    const days=Math.max(0,Math.round(((t.exitT||0)-(t.entryT||0))/86400000));
    return `<div class="trade"><div class="trHead" data-act="tg" data-id="${id}">
      <span><b style="color:${t.dir===-1?'#ff7eb6':'#9ff0c4'}">${t.sym}${t.dir===-1?' SHORT':''}</b> <small style="color:#7d827d">${fmtD(t.exitT)} · ${nameOf(t.setup)}</small></span><b style="color:${c}">${money(t.usd)} <small style="font-weight:600">${t.ret>=0?'+':''}${t.ret.toFixed(1)}%</small></b></div>
      <div id="${id}" class="trDet">
        <div class="trd"><span>Bought → sold</span><b>${botPx(t.entry)} → ${botPx(t.exit)}</b></div>
        <div class="trd"><span>Held</span><b>${fmtD(t.entryT)} → ${fmtD(t.exitT)} · ${days} day${days===1?'':'s'}</b></div>
        ${t.cost!=null?`<div class="trd"><span>Amount</span><b>${fmt(t.cost)}</b></div>`:''}
        <div class="trd"><span>Why it closed</span><b style="text-align:right">${BOT_REASON_TXT[t.reason]||t.reason}</b></div>
        ${t.localManual?'':`<div class="trd"><span>Account after</span><b>${fmt(t.eqAfter)}</b></div>`}</div></div>`;}).join("");

  const filterTxt=scan?(scan.regimeOn?'<b style="color:#00e676">ON</b> <small style="color:#7d827d">— market healthy, both strategies active</small>'
                                     :'<b style="color:#ffb300">OFF</b> <small style="color:#7d827d">— market weak: the rotation waits in cash, only single-coin trends trade</small>'):'';
  return `<div class="secTitle" style="color:#7fb2e0;font-size:10.5px">🤖 BTC PRO BOT v4 · paper portfolio · 17 coins · fixed rules</div>
    <div class="paper" style="border:1.5px solid #2a5d8e;box-shadow:0 0 32px rgba(41,121,255,.10)">
      <div class="paperTop">
        <div class="paperNow">P&amp;L: <b style="color:${pnlCol(totalPnl)}">${money(totalPnl)}</b> <small style="color:#7d827d">(${totalPct>=0?'+':''}${totalPct.toFixed(2)}%) · account ${fmt(eqNow)}${holdRet!=null?` · just holding BTC ${holdRet>=0?'+':''}${holdRet.toFixed(1)}%`:''}</small></div>
        <button class="logBtn" data-act="botrun">${botBusy?'…':'↻ Check now'}</button>
      </div>
      <canvas id="botEq" style="height:46px;margin-top:8px"></canvas>
      <div class="posGrid" style="margin-top:9px">
        <div><span>Open trades (unrealized)</span><b style="color:${pnlCol(unreal)}">${botPos.length?`${money(unreal)} <small style="color:#7d827d">(${botPos.length})</small>`:'—'}</b></div>
        <div><span>Closed trades (realized)</span><b style="color:${pnlCol(realized)}">${closedN?money(realized):'—'}</b></div>
        <div><span>Total P&amp;L</span><b style="color:${pnlCol(totalPnl)}">${money(totalPnl)} <small style="color:#7d827d">(${totalPct>=0?'+':''}${totalPct.toFixed(2)}%)</small></b></div>
        <div><span>Invested now</span><b>${invPct.toFixed(0)}% <small style="color:#7d827d">· cash ${(100-invPct).toFixed(0)}%</small></b></div>
        <div><span>Started with</span><b>${fmt(startEq)}${st.startDate?` <small style="color:#7d827d">${st.startDate}</small>`:''}</b></div>
        <div><span>Trades so far</span><b>${nTrades}${perWeek!=null?` <small style="color:#7d827d">≈ ${perWeek.toFixed(1)} per week</small>`:''}</b></div>
        ${netDep!==0?`<div><span>Net deposits/withdrawals</span><b>${money(netDep)}</b></div>`:''}
        ${closedN?`<div><span>Trades won</span><b>${winsN} of ${closedN} <small style="color:#7d827d">(${winRate}%)</small></b></div>`:''}
        ${tr.length?`<div><span>Profit factor</span><b>${pf===Infinity?'∞':pf!=null?pf.toFixed(2):'—'} <small style="color:#7d827d">won per $1 lost</small></b></div>
        <div><span>Best / worst trade</span><b><span style="color:#69f0ae">${money(best)}</span> / <span style="color:#ff8a80">${money(worst)}</span></b></div>`:''}
        ${(st.manualPnl||0)!==0?`<div><span>Your manual trades (this device)</span><b style="color:${pnlCol(st.manualPnl)}">${money(st.manualPnl)}</b></div>`:''}
      </div>
      ${cloud?`<div class="ensMeta" style="margin-top:6px;color:#69f0ae">☁️ <b>Running 24/7 in the cloud</b> — works even with all your devices off · last cloud run ${Math.round((Date.now()-st.cloudRunAt)/60000)} min ago <span class="ig" data-act="tip" data-tip="El bot corre en los servidores de GitHub (gratis): cada hora revisa precios y, una vez al día justo después del cierre diario mundial, hace su revisión y opera. Tu Mac y tu iPhone solo muestran lo que hace.">ⓘ</span></div>`:''}
      <div class="ensMeta" style="margin-top:6px">${scan?`Last daily review: <b>${scan.date}</b> · bought <b>${(scan.opened||[]).length}</b> · sold <b>${(scan.closed||[]).length}</b> · Market filter: ${filterTxt}`:'No daily review yet — the first one runs right after the next daily close.'}
        <br>Next review: <b>${nrTxt}</b> <small style="color:#5f6b5f">(automatic, once a day after the world daily close)</small>
        <span class="ig" data-act="tip" data-tip="Bot v4: dos estrategias de REGLAS FIJAS sobre 17 monedas grandes. Una vez al día, al cierre diario: (1) ROTACIÓN — se queda con las monedas más fuertes del momento, solo cuando el mercado general está sano; (2) TENDENCIA — compra cada moneda cuando arranca una tendencia alcista y la vende cuando se debilita. Apuesta menos dinero en las monedas más volátiles. Solo compra (no hace shorts). No usa dinero real.">ⓘ</span></div>
      ${posHtml?`<div class="trList"><div class="trListLbl">OPEN POSITIONS · ${botPos.length} · tap one for details</div>${posHtml}</div>`:`<div class="paperEmpty">${scan?'No open positions right now — the bot is in cash, waiting for its rules to give a buy.':'Fresh account: $100,000 in cash. The first trades appear after the next daily review.'}</div>`}
      ${manHtml}
      <div class="ensBd"><div class="ensBdTitle">The two strategies — record so far <span class="ig" data-act="tip" data-tip="Ganados/total y dinero ganado o perdido por cada estrategia. Lo normal es ganar más o menos 1 de cada 3 trades: muchas pérdidas pequeñas y pocas ganancias grandes que pagan todo. Las reglas NO se cambian por una mala racha — así fue como se validaron.">ⓘ</span></div>
        <div class="ensBdRows">${sleeveHtml}</div>
      </div>
      ${newsHtml}
      ${activity?`<div class="trList"><div class="trListLbl">ACTIVITY · everything the bot did, with P&amp;L</div><div style="max-height:240px;overflow-y:auto">${activity}</div></div>`:''}
      ${changeLog&&changeLog.entries?`<div class="trList"><div class="trListLbl" data-act="tg" data-id="whatsnew" style="cursor:pointer">📋 WHAT'S NEW · qué cambió en cada versión ▾</div>
        <div id="whatsnew" class="trDet" style="display:none;max-height:320px;overflow-y:auto">
        ${changeLog.entries.slice(0,8).map(e=>`<div style="padding:7px 0;border-bottom:1px dashed #1f2937">
          <div style="font-size:11.5px"><b style="color:#7fb2e0">v${e.v}</b> <small style="color:#7d827d">· ${e.fecha}</small> · <b>${e.titulo}</b></div>
          ${(e.cambios||[]).map(c=>`<div class="trd" style="padding:2px 0"><span style="color:#9aa09a;line-height:1.4">· ${c}</span></div>`).join('')}
        </div>`).join('')}</div></div>`:''}
      ${jrows?`<div class="trList"><div class="trListLbl">BOT JOURNAL · ${closedN} closed${winRate!=null?' · '+winRate+'% won':''} · realized ${money(realized)}</div><div style="${botJournalAll?'max-height:360px;overflow-y:auto':''}">${jrows}</div>${all.length>12?`<button class="bigBtn" style="width:100%;margin-top:7px" data-act="botjournal">${botJournalAll?'Show recent only':'Show ALL '+all.length+' trades'}</button>`:''}</div>`:`<div class="paperEmpty">No closed trades yet — every sale will be listed here with its profit or loss.</div>`}
      ${brain?`<div class="paperBtns" style="margin-bottom:2px"><button class="logBtn" data-act="botbuy" style="flex:1;background:#00c853;color:#04140b">🟢 Buy (long)</button><button class="logBtn" data-act="botsell" style="flex:1;background:#ff1744;color:#fff">🔴 Sell (short)</button></div>
      <div class="paperNote" style="margin-top:0;padding-top:0;border:none">Your own paper trade on ${asset} — the bot tells you first whether it agrees. Manual trades are kept apart from the bot's record.</div>`:''}
      <div class="paperBtns" style="flex-wrap:wrap">${cloud?'':`<button class="logBtn" data-act="botdeposit">💵 Add funds</button><button class="logBtn ghost" data-act="botwithdraw">Withdraw</button>`}<button class="logBtn ghost" data-act="botbackup">🗂 Backup</button>${cloud?'':`<button class="logBtn ghost" data-act="botrestore">📥 Restore</button>`}<button class="logBtn ghost" data-act="botexport">⬇ CSV</button>${cloud?'':`<button class="logBtn ghost" data-act="botreset">Reset</button>`}</div>
      <div class="paperNote">Paper trading only — it never places real orders. Fixed rules, tested on 5 years of history without peeking at the future: about 1 trade in 3 wins, and the winners are much bigger than the losers. Losing weeks and months are normal; in that test the account fell 25–35% from its peak at the worst moments before recovering. Costs of ~0.2% per round trip are included.</div>
    </div>`;
}

/* compact always-visible bot status strip shown at the very top of the page */
function botStrip(livePx){
  if(!botState)return '';
  const st=botState;
  const m=botMtm(st,s=>(livePx&&livePx[s]!=null)?livePx[s]:null);
  const tot=m.equity-(st.startEquity||100000)-(st.netDeposits||0);
  const col=tot>0.005?'#00e676':tot<-0.005?'#ff1744':'#ffb300';
  const money=v=>(v<0?'−$':'+$')+Math.abs(v).toLocaleString('en-US',{maximumFractionDigits:Math.abs(v)<100?2:0});
  const bp=(st.positions||[]).filter(p=>p.setup!=='manual');
  const syms=Array.from(new Set(bp.map(p=>p.sym)));
  return `<div class="regime" style="border-color:#2a5d8e;background:linear-gradient(180deg,rgba(41,121,255,.08),rgba(41,121,255,.02))">
    <div class="regDot" style="background:${col}"></div>
    <div style="flex:1"><div class="regT" style="color:#7fb2e0">🤖 BOT · P&amp;L <span style="color:${col}">${money(tot)}</span> · ${bp.length} open</div>
    <div class="regN">${syms.length?syms.slice(0,9).join(' · ')+(syms.length>9?' …':''):'in cash — waiting for a buy'} · next review ${botNextRun(new Date()).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'})}</div></div></div>`;
}

/* ============================ RENDER ============================ */
function render(){
  const R=LABELS.map((_,i)=>computeAll(store[i]));
  const cur=R[sel], plan=buildPlan(cur);
  const ENS=ensembleBuild(store[sel]);
  const ensN=store[sel].c.length-1;
  const ensExp=Math.round((ENS.e[ensN]||0)*100);
  const ensP=Math.round((ENS.P[ensN]||0.5)*100);
  const weeklyNorm=R[LABELS.length-1].norm;

  $("#price").classList.remove("pulse");$("#price").textContent=fmt(cur.price);
  const c1d=store[1].c, chg=((cur.price-c1d[c1d.length-2])/c1d[c1d.length-2])*100;
  const ce=$("#chg");ce.textContent=(chg>=0?"▲ ":"▼ ")+Math.abs(chg).toFixed(2)+"%";ce.style.color=chg>=0?"#00e676":"#ff1744";

  let act,acol,asub;
  if(ensExp>=60){act="BUY";acol="#00e676";asub=ensExp>=80?"Strong — high exposure":"Buy — scale in";}
  else if(ensExp<=25){act="REDUCE";acol="#ff1744";asub="Defensive — little/no exposure";}
  else{act="HOLD";acol="#ffb300";asub="Neutral — partial exposure";}

  const N=R.length;
  const bull=R.filter(r=>r.norm>.15).length, bear=R.filter(r=>r.norm<-.15).length;
  let conf;
  if(bull===N)conf=`All ${N} timeframes agree: up.`;
  else if(bear===N)conf=`All ${N} timeframes agree: down.`;
  else if(bull>bear)conf=bull+" of "+N+" timeframes point up.";
  else if(bear>bull)conf=bear+" of "+N+" timeframes point down.";
  else conf="Timeframes are split — usually better to wait.";

  const mini=R.map((r,i)=>{const c=r.norm>.15?"#00e676":r.norm<-.15?"#ff1744":"#ffb300";const ar=r.norm>.15?"▲":r.norm<-.15?"▼":"■";
    return `<span style="color:${c}">${LABELS[i]} ${ar}</span>`;}).join("");
  const wkT=weeklyNorm>.15?'<b style="color:#00e676">bullish</b>':weeklyNorm<-.15?'<b style="color:#ff1744">bearish</b>':'<b style="color:#ffb300">flat</b>';

  let strength=Math.max(1,Math.min(10,Math.round(ensExp/10)));
  const segs=Array.from({length:10},(_,k)=>`<span style="background:${k<strength?acol:'#1c201c'}"></span>`).join("");
  const reg=marketRegime(), whale=whaleActivity();
  const wEmoji=whale.t==="Accumulating"?"🐋":whale.t==="Distributing"?"🔻":"🐳";
  const regimeHtml=`<div class="regime" style="border-color:${reg.c}">
    <div class="regDot" style="background:${reg.c}"></div>
    <div><div class="regT" style="color:${reg.c}">${reg.t}</div><div class="regN">${reg.note}</div></div></div>`;
  const whaleHtml=`<div class="whale">
    <div class="whaleTop"><div class="whaleEmoji">${wEmoji}</div>
      <div><div class="whaleT" style="color:${whale.c}">Whales: ${whale.t}</div>
      <div class="whaleN">${whale.note}${whale.spikes?` · ${whale.spikes} big-volume day(s) in the last 10`:''}</div></div></div>
    <div class="whaleSub">Estimated from trading volume &amp; On-Balance Volume — a proxy for large-player flow, not direct wallet tracking.</div></div>`;

  const ser=signalNormSeries(store[sel]);
  const len=store[sel].c.length, ts=store[sel].t;
  const perDay=[2,1,1/3,1/7][sel];
  const rngDays={'3M':90,'1Y':365,'4Y':1460,'all':Infinity}[rangeKey];
  const winN=rngDays===Infinity?len:Math.min(len,Math.max(30,Math.round(rngDays*perDay)));
  const wStart=Math.max(0,len-winN);
  const spanDays=(ts[len-1]-ts[wStart])/86400000;
  const spanLabel=spanDays>=360?(spanDays/365).toFixed(1).replace('.0','')+'y':Math.round(spanDays)+'d';
  const C=store[sel].c, Hs=store[sel].h, Ls=store[sel].l;
  const chartData=[]; for(let j=wStart;j<len;j++)chartData.push({o:j>0?C[j-1]:C[j],h:Hs[j],l:Ls[j],price:C[j],st:ser.stLine[j],stDir:ser.stDir[j],t:ts[j]});
  const bt=backtest(ser, store[sel], 1, 'sttrend', wStart, 0, false);
  const hold=holdStats(store[sel].c, wStart);
  const liveState=ensExp>=50?'LONG':'FLAT';
  window.__live={asset,tf:LABELS[sel],state:liveState,act,price:cur.price};
  if(storageOK){const sk="ptState_"+asset+"_"+LABELS[sel];let prev=null;try{prev=localStorage.getItem(sk);}catch(e){}
    if(prev==null){try{localStorage.setItem(sk,liveState);}catch(e){}}
    else if(prev!==liveState){const l=loadLog();l.push({ts:Date.now(),asset,tf:LABELS[sel],action:liveState==='LONG'?'BUY':'SELL',price:cur.price,auto:true});saveLog(l);try{localStorage.setItem(sk,liveState);}catch(e){}}}
  const ev=[]; bt.trades.forEach(t=>{ev.push({idx:t.inIdx,type:t.dir===1?'buy':'sell'});ev.push({idx:t.outIdx,type:t.dir===1?'sell':'buy'});});
  if(bt.openTrade)ev.push({idx:bt.openTrade.inIdx,type:bt.openTrade.dir===1?'buy':'sell'});
  const markers=ev.filter(e=>e.idx>=wStart).map(e=>({ci:e.idx-wStart,type:e.type}));
  const rangeBtns=[['3M','3M'],['1Y','1Y'],['4Y','4Y'],['all','All']].map(([k,n])=>`<button class="thb${k===rangeKey?' on':''}" data-act="range" data-k="${k}">${n}</button>`).join("");
  const ensBt=simSized(store[sel],ENS.e,wStart,0.002);
  const ensHoldSh=holdSharpe(store[sel].c,store[sel].t,wStart);

  const btHtml=`<div class="secTitle">ENSEMBLE · WHAT TO DO NOW · ${LABELS[sel]}</div>
    <div class="bt">
      <div class="ensRec">
        <div class="ensTop"><span>🧠 ENSEMBLE SIGNAL</span><b style="color:${ensExp>=66?'#00e676':ensExp>=33?'#ffb300':'#ff7043'}">${ensP}% <small style="font-weight:600;opacity:.85">chance up</small> <span class="ig" data-act="tip" data-tip="Probabilidad combinada de que el precio suba desde aqui. 50% es neutral; mas alto es mas alcista.">ⓘ</span></b></div>
        <div class="ensExp"><div class="ensBarWrap"><div class="ensBar" style="width:${ensExp}%;background:${ensExp>=66?'#00e676':ensExp>=33?'#ffb300':'#ff7043'}"></div></div><span class="ensExpLbl">How much to invest: <b>${ensExp}%</b> <span class="ig" data-act="tip" data-tip="Cuanto de tu capital sugiere tener invertido ahora, de 0% (en efectivo) a 100% (todo dentro). Sale de la probabilidad y del riesgo.">ⓘ</span></span></div>
        <div class="ensMeta">Bigger trend (weekly): <b style="color:${ENS.weekly>=0?'#69f0ae':'#ff8a80'}">${ENS.weekly>=0?'up ▲':'down ▼'}</b> <span class="ig" data-act="tip" data-tip="Tendencia de fondo en grafico semanal. Si va a la baja, el sistema recorta la exposicion para protegerte.">ⓘ</span></div>
        <div class="ensBd"><div class="ensBdTitle">Why this number — what each signal says now <span class="ig" data-act="tip" data-tip="Estas son las 5 senales que se combinan en la probabilidad. Verde = a favor de subir, rojo = a favor de bajar, gris = neutral. Cada una pesa segun su acierto historico.">ⓘ</span></div>
          <div class="ensBdRows">${ENS.breakdown.map(b=>`<span class="bdChip"><i style="background:${b.dir>0?'#00e676':b.dir<0?'#ff5c7a':'#7d827d'}"></i>${b.name} ${b.dir>0?'▲':b.dir<0?'▼':'■'}</span>`).join('')}</div>
          <div class="ensBdNote">Trend strength (ADX): <b>${Math.round(ENS.adx)}</b> ${ENS.adx>=25?'· strong move':'· weak — signals trusted less'}</div></div>
        <div class="ensStats">Tested on this range — return <b style="color:${ensBt.total>=0?'#00e676':'#ff1744'}">${ensBt.total>=0?'+':''}${ensBt.total.toFixed(0)}%</b> <span class="ig" data-act="tip" data-tip="Lo que habria ganado el ensemble en el rango que ves arriba (3M, 1A, 4A...). Ojo: en rangos largos incluye el periodo donde aprendio sus pesos, asi que tiende a verse mejor de lo real.">ⓘ</span> · worst drop <b style="color:#ff8a80">${ensBt.maxDD.toFixed(0)}%</b> <span class="ig" data-act="tip" data-tip="La peor caida desde un maximo en ese periodo (drawdown). Mas cerca de 0% es mejor.">ⓘ</span> · Sharpe <b>${ensBt.sharpe.toFixed(2)}</b> <span class="ig" data-act="tip" data-tip="Retorno ajustado al riesgo. Mas alto es mejor; arriba de 1 es bueno.">ⓘ</span> · MAR <b>${ensBt.mar.toFixed(2)}</b> <span class="ig" data-act="tip" data-tip="Retorno anual dividido por la peor caida. Cuanto ganas por cada punto de riesgo.">ⓘ</span></div>
        <div class="ensStats sub">Just holding the same time: ${hold.ret>=0?'+':''}${hold.ret.toFixed(0)}% · worst drop ${hold.maxDD.toFixed(0)}% · Sharpe ${ensHoldSh.toFixed(2)}</div>
        <div class="ensUpd">↻ Updated ${new Date().toLocaleTimeString()} · live from Binance</div>
      </div>
      <div class="btFoot">"How much to invest" goes 0–100% and already counts ~0.2% fees. The numbers compare the ensemble vs just buying and holding over the range you picked above.</div>
    </div>`;
  const pctv=t=>(t-cur.price)/cur.price*100;
  const kzRow=(lbl,val,col)=>`<div class="lvRow"><span class="lvTag" style="color:${col}">${lbl}</span><span>${fmt(val)} <small style="color:#7d827d">(${pctv(val)>=0?'+':''}${pctv(val).toFixed(1)}%)</small></span></div>`;
  const kzHtml=`<div class="secTitle">KEY PRICE ZONES</div><div class="levels">
    ${kzRow('STRONG RESISTANCE',plan.buyTgts[1],'#ff5c7a')}
    ${kzRow('NEAR RESISTANCE',plan.buyTgts[0],'#ff8a80')}
    <div class="lvRow"><span class="lvTag" style="color:#cfd3cf;background:#1c201c">PRICE NOW</span><span style="font-weight:800">${fmt(cur.price)}</span></div>
    ${kzRow('NEAR SUPPORT',plan.sellTgts[0],'#69f0ae')}
    ${kzRow('STRONG SUPPORT',plan.sellTgts[1],'#34d990')}
  </div>`;
  const val=valuationZone(store[1].c);
  const bnc=bounceStats(store[3].c);
  const valHtml = val ? `<div class="secTitle">VALUATION · ${asset}</div>
    <div class="valCard">
      <div class="valTop"><span style="color:${val.color}">${val.label}</span></div>
      <div class="valGauge"><div class="valMark" style="left:${(val.pos*100).toFixed(0)}%"></div></div>
      <div class="valEnds"><span>◀ cheap</span><span>expensive ▶</span></div>
      <div class="valNote">Price is <b style="color:${val.color}">${val.pct>=0?'+':''}${Math.round(val.pct)}%</b> ${val.pct>=0?'above':'below'} its long-term trend line (≈ ${fmt(val.line)}). <span class="ig" data-act="tip" data-tip="Compara el precio con su linea de crecimiento historica (regresion de largo plazo). Debajo de la linea = barato, encima = caro. Ubica, no predice.">ⓘ</span></div>
      ${bnc&&bnc.isDrop&&bnc.prob!=null?`<div class="bounceLine">📉 Down <b>${Math.abs(bnc.cur).toFixed(1)}%</b> this week. After similar weekly drops, ${asset} rose the next week <b style="color:${bnc.prob>=50?'#00e676':'#ff8a80'}">${Math.round(bnc.prob)}%</b> of the time (avg <b style="color:${bnc.avg>=0?'#69f0ae':'#ff8a80'}">${bnc.avg>=0?'+':''}${bnc.avg.toFixed(1)}%</b> · ${bnc.n} cases). <span class="ig" data-act="tip" data-tip="De las semanas que cayeron asi o mas, cuantas subieron la semana siguiente. Estadistica historica, no garantia.">ⓘ</span></div>`:(bnc&&!bnc.isDrop?`<div class="bounceLine sub">No weekly drop right now (${bnc.cur>=0?'+':''}${bnc.cur.toFixed(1)}% this week). The bounce stat appears after a drop.</div>`:'')}
    </div>` : '';

  let minerHtml='';
  if(asset==='BTC'&&minerCost){
    const mc=minerCost, p=cur.price;
    const inZone=p<=mc.high, below=p<mc.mid;
    const col=p<mc.low?'#00e676':p<mc.high?'#ffb300':'#69f0ae';
    const pctMid=((p/mc.mid-1)*100);
    minerHtml=`<div class="secTitle">MINER BREAK-EVEN · BTC</div>
    <div class="valCard">
      <div class="valTop"><span style="color:${col}">≈ ${fmt(mc.low)} – ${fmt(mc.high)}</span> <small style="color:#7d827d;font-weight:400">est. cost to mine 1 BTC</small></div>
      <div class="valNote">Price now is <b style="color:${col}">${pctMid>=0?'+':''}${Math.round(pctMid)}%</b> ${pctMid>=0?'above':'below'} the central estimate (≈ ${fmt(mc.mid)}). ${below?'<b style="color:#ffb300">Near/below miner cost</b> — historically a strong floor (miners stop selling).':'Comfortably above miner cost.'} <span class="ig" data-act="tip" data-tip="Estimación del costo de ELECTRICIDAD para producir 1 BTC, según el hashrate real de la red (mempool.space) a 0.04–0.06 \$/kWh y eficiencia ~25 J/TH. Es una ESTIMACIÓN, no un dato exacto; el costo total (con máquinas) es mayor. Cuando el precio cae cerca de esta zona los mineros dejan de vender y suele actuar como piso.">ⓘ</span></div>
      <div class="btFoot">Network hashrate ${mc.hashrateEH} EH/s · electricity-only · assumes ~25 J/TH. Updated ${new Date(mc.at).toLocaleDateString(undefined,{month:'short',day:'numeric'})}.</div>
    </div>`;
  }

  const botHtml=renderBot(cur.price);

  const log=loadLog();
  const logRows=log.slice(-40).reverse().map(e=>{const c=e.action==='BUY'?'#00e676':e.action==='SELL'?'#ff1744':'#ffb300';
    const d=new Date(e.ts).toLocaleDateString(undefined,{year:'2-digit',month:'short',day:'numeric'});
    return `<div class="logRow"><span class="logD">${d}</span><span class="logA">${e.asset} · ${e.tf}</span><span class="logAct" style="color:${c}">${e.action}</span><span class="logP">${fmt(e.price)}</span><span class="logK">${e.auto?'auto':'manual'}</span></div>`;}).join("");
  const paperHtml=`<div class="secTitle">SIGNAL LOG · your forward record</div>
    <div class="paper">
      <div class="paperTop">
        <div class="paperNow">Now: <b style="color:${liveState==='LONG'?'#00e676':'#ffb300'}">${liveState==='LONG'?'● EXPOSED '+ensExp+'%':'○ DEFENSIVE '+ensExp+'%'}</b> · ${asset} ${LABELS[sel]} · ${act}</div>
        <button class="logBtn" data-act="lognow">📌 Log this</button>
      </div>
      ${storageOK?'':`<div class="paperWarn">⚠ This browser is blocking local storage, so the log won't persist between sessions. Use Export CSV to keep it.</div>`}
      ${logRows?`<div class="logList">${logRows}</div>
        <div class="paperBtns"><button class="logBtn ghost" data-act="exportlog">⬇ Export CSV</button><button class="logBtn ghost" data-act="clearlog">Clear</button></div>`
        :`<div class="paperEmpty">No entries yet. The app auto-logs each time the ${asset} ${LABELS[sel]} ensemble flips between exposed and defensive — just open it regularly. Or tap "Log this" to capture the current state.</div>`}
      <div class="paperNote">Records the ensemble's calls going forward — the only evidence that isn't hindsight. An entry is auto-added whenever the ensemble crosses 50% exposure (exposed ↔ defensive). Switch the asset/timeframe above to track different markets.</div>
    </div>`;

  let sentHtml="";
  if(sentiment){const sv=last(sentiment),col=sentColor(sv.v);
    sentHtml=`<div class="sentLine"><span class="big" style="color:${col}">${sv.v}</span>
      <div><b style="color:${col}">${sv.cls}</b> · market sentiment<br>
      <span style="color:#7d827d;font-size:10px">Fear &amp; Greed (0–100). Measures emotion, not price.</span></div></div>`;}

  const groups=["Momentum","Trend","Volatility","Volume"];
  const detail=groups.map(g=>{const items=cur.cards.filter(c=>c.g===g).map(c=>{const col=c.score>0?"#00e676":c.score<0?"#ff1744":"#ffb300";
    return `<div class="ind" style="border-left-color:${col}"><div class="indTop"><span class="indName">${c.n}</span>
      <span class="indVal" style="color:${col}">${c.val}</span></div><div class="indState" style="color:${col}">${c.st}</div>
      <div class="indNote">${c.note}</div></div>`;}).join("");
    return `<div class="secTitle">${g.toUpperCase()}</div><div class="grid">${items}</div>`;}).join("");

  $("#content").innerHTML=`
    ${botStrip({[asset]:cur.price})}
    ${chartHidden?`<div class="chartCard collapsed">
      <div class="chartTitle"><span>${asset} price chart</span><button class="bigBtn" data-act="togglechart">📈 Show chart</button></div></div>`:`<div class="chartCard">
      <div class="chartTitle"><span>${asset} · price &amp; trend flips · showing ${spanLabel}</span><span style="display:flex;gap:6px"><button class="bigBtn" data-act="togglechart">Hide</button><button class="bigBtn" id="bigBtn" data-act="bigchart">${chartBig?'✕ Close':'⛶ Expand'}</button></span></div>
      <div class="rangeRow">${rangeBtns}</div>
      <div id="cvInfo" class="cvInfo">Hover a candle to see its date &amp; price · scroll to zoom · drag to pan</div>
      <canvas id="cv"></canvas></div>`}

    <div class="cols">
      <div class="sec">${botHtml}</div>

      <div class="sec">${regimeHtml}
        <div class="hero" style="border-color:${acol};box-shadow:0 0 30px ${acol}22">
          <div class="heroLbl">SIGNAL NOW · ${LABELS[sel]}</div>
          <div class="heroAct" style="color:${acol}">${act}</div>
          <div class="heroSub">${asub}</div>
          <div class="conf10"><span class="c10lbl" style="color:${acol}">Confidence ${strength}/10</span><div class="confBar">${segs}</div></div>
          <div class="heroConf">${conf}<div class="miniTf">${mini}</div>
            <div class="wkNote">Weekly trend: ${wkT} — when it's down, the ensemble cuts how much to invest.</div></div>
        </div></div>

      <div class="sec">${btHtml}</div>

      <div class="sec">${kzHtml}</div>

      <div class="sec">${valHtml}</div>

      ${minerHtml?`<div class="sec">${minerHtml}</div>`:''}

      <div class="sec">${paperHtml}</div>

      <div class="sec">${whaleHtml}</div>

      <div class="sec">${sentHtml}
        <button class="detailBtn" data-act="toggledetail" id="dbtn">Show 12 indicators in detail ▾</button>
        <div id="detail">${detail}</div></div>
    </div>

    <div class="foot">◉ ${new Date().toLocaleTimeString()} · auto every 2 min · Binance + alternative.me</div>`;
  chartState={full:chartData,plan,markers,view:{a:0,b:chartData.length},hover:-1};
  if(!chartHidden) requestAnimationFrame(()=>setupChart());
  requestAnimationFrame(()=>drawBotEq());
}

function renderTF(){const row=$("#tfRow");row.innerHTML="";LABELS.forEach((l,i)=>{
  const b=document.createElement("button");b.className="tfBtn"+(i===sel?" active":"");b.textContent=l;
  b.onclick=()=>{sel=i;renderTF();if(store[sel])render();};row.appendChild(b);});}

function renderAssets(){const row=$("#assetRow");if(!row)return;row.innerHTML="";ASSETS.forEach(([sym])=>{
  const b=document.createElement("button");b.className="tfBtn"+(sym===asset?" active":"");b.textContent=sym;
  b.onclick=()=>{ if(sym===asset)return; asset=sym; renderAssets();
    const h=document.getElementById("h1title");if(h)h.innerHTML=sym+' <small>PRO</small>';
    const k=document.getElementById("kicker");if(k)k.textContent=sym+' · SIGNALS';
    const p=document.getElementById("price");if(p){p.textContent="————";p.classList.add("pulse");}
    store={}; go(); };
  row.appendChild(b);});}

/* ---- paper signal log (persists in the browser the file runs in) ---- */
let storageOK=(()=>{try{localStorage.setItem("__t","1");localStorage.removeItem("__t");return true;}catch(e){return false;}})();
function loadLog(){try{return JSON.parse(localStorage.getItem("ptLog")||"[]");}catch(e){return[];}}
function saveLog(a){try{localStorage.setItem("ptLog",JSON.stringify(a.slice(-300)));}catch(e){}}
function downloadCSV(rows,name){
  const csv=rows.map(r=>r.join(",")).join("\n");const blob=new Blob([csv],{type:"text/csv"});
  const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=name;a.click();
}

/* ---- one delegated click handler: CSP-safe, no inline onclick ---- */
function showTip(t){let el=document.getElementById("tipBox");
  if(!el){el=document.createElement("div");el.id="tipBox";document.body.appendChild(el);}
  el.textContent=t;el.style.display="block";}
document.addEventListener("click",async e=>{
  const el=e.target.closest("[data-act]");
  const tip=document.getElementById("tipBox");
  if(tip&&!(el&&el.dataset.act==="tip"))tip.style.display="none";
  if(!el)return;
  switch(el.dataset.act){
    case "tip": showTip(el.dataset.tip); break;
    case "tg": {const d=document.getElementById(el.dataset.id);if(d)d.style.display=d.style.display==="block"?"none":"block"; break;}
    case "range": rangeKey=el.dataset.k; if(store[sel])render(); break;
    case "togglechart": chartHidden=!chartHidden; if(store[sel])render(); break;
    case "bigchart": chartBig=!chartBig;{const card=document.querySelector(".chartCard");if(card)card.classList.toggle("big",chartBig);
      const b=document.getElementById("bigBtn");if(b)b.textContent=chartBig?"✕ Close":"⛶ Expand";setupChart();} break;
    case "toggledetail": {const d=$("#detail"),b=$("#dbtn");const open=d.style.display==="block";
      d.style.display=open?"none":"block";b.textContent=open?"Show 12 indicators in detail ▾":"Hide detail ▴"; break;}
    case "lognow": {const L=window.__live;if(!L)break;const l=loadLog();
      l.push({ts:Date.now(),asset:L.asset,tf:L.tf,action:L.act,price:L.price,auto:false});saveLog(l);if(store[sel])render(); break;}
    case "exportlog": {const l=loadLog();if(!l.length)break;
      downloadCSV([["date","asset","timeframe","action","price","type"]].concat(l.map(x=>[new Date(x.ts).toISOString().slice(0,10),x.asset,x.tf,x.action,x.price,x.auto?"auto":"manual"])),"signal-log.csv"); break;}
    case "clearlog": {if(typeof confirm==="function"&&!confirm("Clear the entire signal log?"))break;saveLog([]);
      try{Object.keys(localStorage).filter(k=>k.indexOf("ptState_")===0).forEach(k=>localStorage.removeItem(k));}catch(err){}
      if(store[sel])render(); break;}
    case "botrun": {if(botBusy)break;botBusy=true;if(store[sel])render();
      try{const r=await botCheckExits();botState=(r&&r.state)||await botLoad();botSetBadge(botState);}catch(err){}
      botBusy=false;if(store[sel])render(); break;}
    case "botexport": {if(!botState||!botState.trades.length)break;
      const day=t=>t?new Date(t).toISOString().slice(0,10):"";
      downloadCSV([["opened","closed","asset","strategy","direction","amount_usd","entry","exit","return_pct","pnl_usd","exit_reason","account_after"]]
        .concat(botState.trades.map(t=>
          [day(t.entryT),day(t.exitT),t.sym,t.setup,t.dir===-1?"SHORT":"LONG",t.cost!=null?t.cost:"",t.entry,t.exit,t.ret,t.usd,t.reason,t.localManual?"":t.eqAfter])),"btc-pro-bot-journal.csv"); break;}
    case "botjournal": {botJournalAll=!botJournalAll;if(store[sel])render();break;}
    case "botdeposit": {if(!botState)break;
      const v=parseFloat(prompt("Amount to ADD to the paper account (USD):","5000"));
      if(!isFinite(v)||v<=0)break;
      await botQueue(async()=>{const stf=await botLoad();
        stf.netDeposits=(stf.netDeposits||0)+v;
        stf.equity=+(stf.equity+v).toFixed(2);
        stf.cashFlows=(stf.cashFlows||[]).concat([{ts:Date.now(),amt:v}]).slice(-50);
        botLog(stf,'info','Deposit: +$'+v.toLocaleString('en-US'));
        await botSave(stf);botState=stf;});
      if(store[sel])render();break;}
    case "botwithdraw": {if(!botState)break;
      const v=parseFloat(prompt("Amount to WITHDRAW from the paper account (USD):","1000"));
      if(!isFinite(v)||v<=0)break;
      if(botState.equity-v<100){alert("Leave at least $100 in the account so the bot can keep trading.");break;}
      await botQueue(async()=>{const stf=await botLoad();
        if(stf.equity-v<100)return;
        stf.netDeposits=(stf.netDeposits||0)-v;
        stf.equity=+(stf.equity-v).toFixed(2);
        stf.cashFlows=(stf.cashFlows||[]).concat([{ts:Date.now(),amt:-v}]).slice(-50);
        botLog(stf,'info','Withdrawal: −$'+v.toLocaleString('en-US'));
        await botSave(stf);botState=stf;});
      if(store[sel])render();break;}
    case "botbackup": {if(!botState)break;
      const blob=new Blob([JSON.stringify(botState,null,1)],{type:"application/json"});
      const a=document.createElement("a");a.href=URL.createObjectURL(blob);
      a.download="btc-pro-bot-backup-"+botDayStr(new Date())+".json";a.click();break;}
    case "botrestore": {const inp=document.createElement("input");inp.type="file";inp.accept=".json,application/json";
      inp.onchange=async()=>{const f=inp.files&&inp.files[0];if(!f)return;
        try{
          const obj=JSON.parse(await f.text());
          if(!obj||obj.startEquity==null||!(obj.version>=4))throw 0;
          if(typeof confirm==="function"&&!confirm("Replace the bot's current data with this backup?"))return;
          await botSave(botMigrate(obj));botState=await botLoad();botSetBadge(botState);if(store[sel])render();
          alert("Backup restored ✓");
        }catch(e){alert("That file is not a BTC Pro v4 backup (older backups belong to the previous bot and can't be loaded).");}};
      inp.click();break;}
    case "botreset": {if(typeof confirm==="function"&&!confirm("Reset the bot? This erases its paper record and starts again with $100,000."))break;
      await botQueue(async()=>{await botSave(botDefaultState());});
      botState=await botLoad();botSetBadge(botState);
      if(store[sel])render(); break;}
    case "botclose": {
      if(!botState)break;
      const id=+el.dataset.id;
      const pos=(botState.positions||[]).find(p=>p.id===id);
      if(!pos)break;
      const isMan=pos.setup==='manual';
      if(!isMan&&botCloudFresh(botState)){
        alert("Esta posición la gestiona el bot de la nube (24/7) y se cierra sola por sus reglas. Solo tus trades manuales se cierran desde aquí.");break;}
      // best available live price for this position's asset
      const px=(pos.sym===asset&&store[1])?store[1].c[store[1].c.length-1]:((botState.lastPx&&botState.lastPx[pos.sym])||pos.entry);
      const pl=botPosPnl(botState,pos,px);
      let verdict;
      if(!isMan)verdict='⚠️ WARNING: the bot’s rules would KEEP this trade open today. Closing it now goes AGAINST its plan.';
      else{
        // second opinion: what does the bot think about this symbol right now?
        const v=(pos.sym===asset&&store[1])?botView(store[1],botState):null;
        const act=v?v.action:'FLAT';
        const same=(pos.dir===1&&act==='LONG')||(pos.dir===-1&&act==='SHORT');
        const opp=(pos.dir===1&&act==='SHORT')||(pos.dir===-1&&act==='LONG');
        verdict=same?'⚠️ WARNING: the bot still sees '+pos.sym+' trending '+(act==='LONG'?'UP':'DOWN')+' — it would KEEP this trade open. Closing now goes AGAINST its read.'
          :opp?'✅ The bot now sees '+pos.sym+' trending '+(act==='LONG'?'UP':'DOWN')+' — closing is IN LINE with its read.'
          :'➖ The bot has no clear read on '+pos.sym+' right now.';
        if(pos.scaled)verdict+='\n🛡️ This trade is already protected — stop at breakeven + trailing.';
      }
      const m=pos.sym+' '+(pos.dir===1?'LONG':'SHORT')+' at '+botPx(px)+
        '\n\nClosing now locks in '+(pl.usd>=0?'+$':'−$')+Math.abs(pl.usd).toLocaleString('en-US',{maximumFractionDigits:2})+
        ' ('+(pl.pct>=0?'+':'')+pl.pct.toFixed(1)+'%).'+
        '\n\n'+verdict+
        '\n\nThis is PAPER trading. Close this trade now?';
      if(typeof confirm==='function'&&!confirm(m))break;
      await botQueue(async()=>{const stf=await botLoad();
        const p=(stf.positions||[]).find(q=>q.id===id);
        if(p)botCloseTrade(stf,p,px,Date.now(),'manual');
        await botSave(stf);botState=stf;botSetBadge(stf);});
      if(store[sel])render(); break;}
    case "botbuy": case "botsell": {
      if(!botState||!store[1])break;
      const dir=el.dataset.act==='botbuy'?1:-1, price=store[1].c[store[1].c.length-1];
      const view=botView(store[1],botState);
      if(!view){alert("Not enough data to open a trade yet.");break;}
      const plan=botManualPlan(price,view.atrPct,dir);
      const aligned=(dir===1&&view.action==='LONG')||(dir===-1&&view.action==='SHORT');
      const against=(dir===1&&view.action==='SHORT')||(dir===-1&&view.action==='LONG');
      const fights=view.nearTrend!==0&&view.nearTrend!==dir;
      const yourMove=dir===1?'BUY (go LONG — bet it goes UP)':'SELL (go SHORT — bet it goes DOWN)';
      const botSays=view.action==='FLAT'?'NO CLEAR TREND':(view.action==='LONG'?'UPTREND':'DOWNTREND');
      let verdict;
      if(view.action==='FLAT') verdict='➖ The bot sees no clear trend on '+asset+' right now — no edge either way.';
      else if(aligned) verdict='✅ This AGREES with the bot — you’re on the same side as the trend it sees.';
      else if(against) verdict='⚠️ WARNING: this goes AGAINST the bot. It sees '+asset+' in a'+(view.action==='LONG'?'n UPTREND':' DOWNTREND')+' right now.';
      else verdict='➖ The bot has no strong opinion on this direction.';
      const trendNote=fights?'\n⚠️ It also fights the '+(view.nearTrend>0?'UP':'DOWN')+' move of the last 2 weeks.':'';
      const msg=asset+' — '+yourMove+' at '+botPx(price)+
        '\n\nThe bot says: '+botSays+'\n'+verdict+trendNote+
        '\n\nPlan (paper): size '+plan.sizePct+'% of the account · stop '+botPx(plan.stop)+
        ' · target '+botPx(plan.t2)+' · risk ~1.5% of the account.'+
        '\nManual trades are tracked apart from the bot’s own record.'+
        '\n\nThis is PAPER trading — no real money. Open this trade?';
      if(typeof confirm==='function'&&!confirm(msg))break;
      await botQueue(async()=>{const stf=await botLoad();
        botOpenManual(stf,asset,dir,price,view);await botSave(stf);botState=stf;botSetBadge(stf);});
      if(store[sel])render(); break;}
  }
});

function showErr(m){const e=$("#err");if(m){e.style.display="block";e.innerHTML="⚠ "+m;}else e.style.display="none";}
let goBusy=false;
async function go(){
  if(goBusy)return; goBusy=true;
  try{ await _go(); }finally{ goBusy=false; }
}
async function _go(){
  $("#refresh").classList.add("spin");showErr(null);
  if(!$("#content").innerHTML.trim()) $("#content").innerHTML='<div class="loadingBox">⏳ Loading live market data…</div>';
  try{
    store=await loadStoreFor(asset);
    sentiment=await fetchSentiment(30);
    if(!minerCost||Date.now()-minerCost.at>6*3600000){try{const mc=await fetchMinerCost();if(mc)minerCost=mc;}catch(e){}}
    if(!changeLog){try{const r=await fetch('https://jlsv305-droid.github.io/btc-pro/changelog.json',{cache:'no-store'});if(r.ok)changeLog=await r.json();}catch(e){}}
    if(!botState)botState=await botEnsureReady();
    try{const cs=await botSyncCloud();if(cs)botState=cs;}catch(e){} // mirror the 24/7 cloud bot when reachable
    if(!botCloudFresh(botState)&&botNeedsRun(botState)){    // local daily review only if the cloud has gone silent
      try{const r=await botRunMorning({});if(r.state)botState=r.state;}catch(e){}
    }
    botSetBadge(botState);
    $("#refresh").classList.remove("spin");
    render();
  }catch(e){$("#refresh").classList.remove("spin");
    if(e&&e.rate)showErr("The data provider is rate-limiting requests. Wait ~1 min and tap refresh.");
    else showErr("Couldn't load price data. Check your connection and try again.");}
}
$("#refresh").onclick=go;
renderAssets(); renderTF(); go(); setInterval(go,120000);
let rt;window.addEventListener("resize",()=>{clearTimeout(rt);rt=setTimeout(()=>{const cv=$("#cv");if(cv&&store[sel])render();},200);});
