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
let sel=1, store={}, sentiment=null, asset='BTC';
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

/* ============================ MORNING BOT CARD ============================ */
function drawBotEq(){
  const cv=document.getElementById('botEq'); if(!cv||!botState)return;
  const eq=[botState.startEquity||10000].concat(botState.trades.map(t=>t.eqAfter));
  if(eq.length<2)return;
  const dpr=window.devicePixelRatio||1,w=cv.clientWidth||300,H=46;
  cv.width=w*dpr;cv.height=H*dpr;const ctx=cv.getContext('2d');ctx.scale(dpr,dpr);
  const mn=Math.min(...eq),mx=Math.max(...eq);
  const X=i=>i/(eq.length-1)*(w-4)+2, Y=v=>4+(1-(v-mn)/((mx-mn)||1))*(H-8);
  ctx.beginPath();eq.forEach((v,i)=>{i?ctx.lineTo(X(i),Y(v)):ctx.moveTo(X(i),Y(v));});
  ctx.strokeStyle=eq[eq.length-1]>=eq[0]?'#00e676':'#ff1744';ctx.lineWidth=1.6;ctx.stroke();
}
function renderBot(curPrice){
  if(!botState)return `<div class="secTitle">🤖 MORNING BOT · paper trading</div><div class="paper"><div class="paperEmpty">Starting up the bot…</div></div>`;
  const st=botState, scan=st.lastScan, isExt=(typeof chrome!=='undefined'&&chrome.alarms);
  const nr=botNextRun(new Date());
  const nrTxt=nr.toLocaleDateString(undefined,{weekday:'short',month:'short',day:'numeric'})+' '+nr.toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
  const startEq=st.startEquity||10000;
  let _pe=startEq;
  const tr=st.trades.map(t=>{const dollars=t.eqAfter-_pe;_pe=t.eqAfter;return Object.assign({},t,{dollars});});
  const wins=tr.filter(t=>t.ret>0).length;
  const winRate=tr.length?Math.round(wins/tr.length*100):null;
  const netDep=st.netDeposits||0;
  const realized=st.equity-startEq-netDep;
  const pxOf=sym=>(sym===asset&&curPrice)?curPrice:(st.lastPx&&st.lastPx[sym])||null;
  /* unrealized P&L across all open positions (banked halves included) */
  const positions=st.positions||[];
  const upnl=positions.map(o=>{
    const ref=pxOf(o.sym)||o.entry;
    const leg=p=>(o.dir===1?(p-o.entry)/o.entry:(o.entry-p)/o.entry)*100;
    const pct=o.scaled?0.5*leg(o.t1)+0.5*leg(ref):leg(ref);
    return {o,pct,usd:st.equity*(pct/100)*(o.sizePct/100)};
  });
  const unreal=upnl.reduce((a,x)=>a+x.usd,0);
  const totalPnl=realized+unreal, totalPct=totalPnl/(startEq+Math.max(0,netDep))*100;
  const gw=tr.filter(t=>t.dollars>0).reduce((a,t)=>a+t.dollars,0);
  const gl=Math.abs(tr.filter(t=>t.dollars<=0).reduce((a,t)=>a+t.dollars,0));
  const pf=tr.length?(gl>0?(gw/gl):(gw>0?Infinity:null)):null;
  const best=tr.length?Math.max(...tr.map(t=>t.dollars)):null;
  const worst=tr.length?Math.min(...tr.map(t=>t.dollars)):null;
  const holdRet=(st.startPrice&&pxOf('BTC'))?((pxOf('BTC')/st.startPrice-1)*100):null;
  const money=v=>(v<0?'−$':'+$')+Math.abs(v).toLocaleString('en-US',{maximumFractionDigits:Math.abs(v)<100?2:0});
  const pnlCol=v=>v>0.005?'#00e676':v<-0.005?'#ff1744':'#ffb300';
  const fmtD=t=>new Date(t).toLocaleDateString(undefined,{month:'short',day:'numeric'});
  const usedRisk=botUsedRisk(st);

  /* per-asset scan summary */
  const scanLine=scan?BOT_ASSETS.map(sym=>{const a=scan.byAsset&&scan.byAsset[sym];if(!a)return '';
    const col=a.action==='LONG'?'#00e676':a.action==='SHORT'?'#ff5c7a':'#ffb300';
    return `<b>${sym}</b> <b style="color:${col}">${a.action}</b> <small style="color:#7d827d">score ${a.score>0?'+':''}${a.score}</small>`;
  }).filter(Boolean).join(' &nbsp;·&nbsp; '):'';

  /* open positions */
  const posHtml=upnl.map(x=>{const o=x.o,isL=o.dir===1,pc=x.pct>=0?'#00e676':'#ff1744';
    const setupName=(BOT_SETUPS.find(s=>s[0]===(o.setup||'morning'))||[0,'—'])[1];
    return `<div class="pos" style="border-color:${pc};margin-top:10px">
      <div class="posTop"><span class="posState" style="color:${isL?'#00e676':'#ff7eb6'}">● ${o.sym} ${isL?'LONG':'SHORT'} · ${o.sizePct}%${o.scaled?' · <small style="color:#69f0ae">50% banked ✓</small>':''}</span>
        <span class="posPnl" style="color:${pc}">${money(x.usd)} <small style="font-weight:600">${x.pct>=0?'+':''}${x.pct.toFixed(1)}%</small></span></div>
      <div class="posGrid">
        <div><span>Setup · opened</span><b>${setupName} · ${o.date}</b></div>
        <div><span>Entry</span><b>${fmt(o.entry)}</b></div>
        <div><span>${o.scaled?'Trailing stop':'Stop loss'}</span><b style="color:${o.scaled?'#ffd54f':'#ff8a80'}">${fmt(o.stop)}${o.scaled?' <small style="color:#7d827d">can’t lose now</small>':''}</b></div>
        ${o.scaled?`<div><span>Final target</span><b style="color:#69f0ae">${fmt(o.t2)}</b></div>`
                  :`<div><span>Target 1 (take 50%)</span><b style="color:#69f0ae">${fmt(o.t1)}</b></div>
        <div><span>Final target</span><b style="color:#69f0ae">${fmt(o.t2)}</b></div>`}
      </div>
    </div>`;}).join('');

  /* pending (armed) orders */
  const pendHtml=(st.pending||[]).map(p=>{
    const tn=p.type==='dip'?'Dip-buy limit':'Breakout stop';
    const exp=new Date(p.expires).toLocaleDateString(undefined,{weekday:'short'})+' '+new Date(p.expires).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
    return `<div class="trd"><span>⏳ ${p.sym} ${p.dir===1?'LONG':'SHORT'} <small style="color:#7d827d">(${tn})</small></span><b>if price touches ${fmt(p.trigger)} <small style="color:#7d827d">· ${p.sizePct}% · expires ${exp}</small></b></div>`;
  }).join('');

  /* setups record */
  const setupHtml=BOT_SETUPS.map(([id,nm])=>{const s=(st.setups||{})[id]||{hits:0,total:0,mult:1};
    const col=s.mult===0?'#ff5c7a':s.mult<1?'#ffd54f':'#7d827d';
    return `<span class="bdChip"><i style="background:${col}"></i>${nm} <b>${s.total?s.hits+'/'+s.total:'0/0'}</b>${s.mult<1?` <small style="color:${col}">${s.mult===0?'off':'½ size'}</small>`:''}</span>`;
  }).join('');

  const curReg=(scan&&scan.byAsset&&scan.byAsset.BTC&&scan.byAsset.BTC.regime)||'bearVol';
  const regW=(st.weightsR&&st.weightsR[curReg])||{};
  const news=st.news;
  const newsHtml=news?`<div class="ensBd"><div class="ensBdTitle">📰 News radar — ${news.n} headlines, last 36h <span class="ig" data-act="tip" data-tip="Titulares de CoinDesk, Cointelegraph y Decrypt puntuados por palabras clave: sentimiento alcista/bajista y riesgo de volatilidad (Fed, hacks, ETF, demandas...). Vota como senal #11 y reduce el tamano 30% cuando el riesgo de evento es alto.">ⓘ</span></div>
    <div class="ensStats">Sentiment: <b style="color:${news.sent>=0.25?'#00e676':news.sent<=-0.25?'#ff5c7a':'#ffb300'}">${news.sent>=0.25?'bullish':news.sent<=-0.25?'bearish':'neutral'} (${news.sent>=0?'+':''}${news.sent})</b> · Event risk: <b style="color:${news.vol>=0.6?'#ff8a80':news.vol>=0.3?'#ffb300':'#69f0ae'}">${news.vol>=0.6?'HIGH — trade sizes cut 30%':news.vol>=0.3?'medium':'low'}</b></div>
    ${(news.top||[]).map(x=>`<div class="trd"><span style="flex:1;line-height:1.35">${x.t}</span><b style="white-space:nowrap;margin-left:8px;color:${x.sent>0?'#69f0ae':x.sent<0?'#ff8a80':'#ffb300'}">${x.sent>0?'▲':x.sent<0?'▼':'•'}${x.vol>=1.5?' ⚡':''} <small style="color:#5f6b5f">${x.src}</small></b></div>`).join('')}
  </div>`:'';
  const study=st.study;
  const studyHtml=study?`<div class="ensBdNote" style="margin-top:7px">🌙 Nightly study (${new Date(study.at).toLocaleDateString(undefined,{month:'short',day:'numeric'})}): tested <b>${study.tested}</b> strategy variants — ${study.adopted?`<b style="color:#69f0ae">adopted new tuning</b> · entry ${study.params.th} · stop ${study.params.stopATR}×ATR · target ${study.params.t2ATR}×ATR · trail ${study.params.trailATR}×ATR`:'kept the current tuning (no variant beat it out-of-sample)'}</div>`:'';
  const wRows=BOT_SIGNALS.map(s=>{const w=regW[s.id]||1;const L=st.learn[s.id]||{hits:0,total:0};
      return {name:s.name,w,acc:L.total>=5?Math.round(L.hits/L.total*100):null};})
    .sort((a,b)=>b.w-a.w)
    .map(r=>`<span class="bdChip"><i style="background:${r.w>=1.05?'#00e676':r.w<=0.95?'#ff5c7a':'#7d827d'}"></i>${r.name} <b>${r.w.toFixed(2)}</b>${r.acc!=null?` <small style="color:#7d827d">${r.acc}% right</small>`:''}</span>`).join('');
  const lessons=(st.lessons||[]).slice(-3).reverse().map(l=>`<div class="trd"><span>${new Date(l.ts).toLocaleDateString(undefined,{month:'short',day:'numeric'})}</span><b>${l.txt}</b></div>`).join('');
  const activity=(st.activity||[]).slice(-20).reverse().map(a=>{
    const col=a.kind==='win'?'#69f0ae':a.kind==='loss'?'#ff8a80':a.kind==='open'?'#7fb2e0':'#9aa09a';
    const d=new Date(a.ts);
    const ds=d.toLocaleDateString(undefined,{month:'short',day:'numeric'})+' '+d.toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'});
    return `<div class="trd"><span style="white-space:nowrap">${ds}</span><b style="color:${col};text-align:right;margin-left:10px">${a.txt}</b></div>`;}).join('');

  const showN=botJournalAll?tr.length:12;
  const jrows=tr.slice(-showN).reverse().map((t,k)=>{const id="bj"+k,c=t.ret>=0?"#00e676":"#ff1744";
    const setupName=(BOT_SETUPS.find(s=>s[0]===(t.setup||'morning'))||[0,'—'])[1];
    return `<div class="trade"><div class="trHead" data-act="tg" data-id="${id}">
      <span><b style="color:${t.dir===-1?'#ff7eb6':'#9ff0c4'}">${t.sym||'BTC'} ${t.dir===-1?'SHORT':'LONG'}</b> ${t.date} · ${t.sizePct}%</span><b style="color:${c}">${money(t.dollars)} <small style="font-weight:600">${t.ret>=0?'+':''}${t.ret.toFixed(1)}%</small></b></div>
      <div id="${id}" class="trDet"><div class="trd"><span>Setup</span><b>${setupName}</b></div>
        <div class="trd"><span>Entry → Exit</span><b>${fmt(t.entry)} → ${fmt(t.exit)}${t.scaled?' <small style="color:#69f0ae">(50% banked at T1)</small>':''}</b></div>
        <div class="trd"><span>Closed</span><b>${fmtD(t.exitT)} · ${t.reason==='stop'?'stop loss':t.reason==='trail'?'trailing stop':t.reason==='target'?'final target':t.reason==='time'?'time limit':'signal flip'}</b></div>
        <div class="trd"><span>Equity after</span><b>${fmt(t.eqAfter)}</b></div></div></div>`;}).join("");

  return `<div class="secTitle" style="color:#7fb2e0;font-size:10.5px">🤖 MORNING BOT · paper portfolio · regime-aware · self-tuning</div>
    <div class="paper" style="border:1.5px solid #2a5d8e;box-shadow:0 0 32px rgba(41,121,255,.10)">
      <div class="paperTop">
        <div class="paperNow">P&amp;L: <b style="color:${pnlCol(totalPnl)}">${money(totalPnl)}</b> <small style="color:#7d827d">(${totalPct>=0?'+':''}${totalPct.toFixed(2)}%) · equity ${fmt(st.equity+unreal)}${holdRet!=null?` · holding ${holdRet>=0?'+':''}${holdRet.toFixed(1)}%`:''}</small></div>
        <button class="logBtn" data-act="botrun">${botBusy?'…':'▶ Scan now'}</button>
      </div>
      <canvas id="botEq" style="height:46px;margin-top:8px"></canvas>
      <div class="posGrid" style="margin-top:9px">
        <div><span>Open trades (unrealized)</span><b style="color:${pnlCol(unreal)}">${positions.length?`${money(unreal)} <small style="color:#7d827d">(${positions.length} position${positions.length>1?'s':''})</small>`:'—'}</b></div>
        <div><span>Closed trades (realized)</span><b style="color:${pnlCol(realized)}">${tr.length?money(realized):'—'}</b></div>
        <div><span>Total P&amp;L</span><b style="color:${pnlCol(totalPnl)}">${money(totalPnl)} <small style="color:#7d827d">(${totalPct>=0?'+':''}${totalPct.toFixed(2)}%)</small></b></div>
        <div><span>Risk in use</span><b>${usedRisk.toFixed(1)}% <small style="color:#7d827d">of ${BOT_RISK_BUDGET}% budget</small></b></div>
        <div><span>Started with</span><b>${fmt(startEq)}${st.startDate?` <small style="color:#7d827d">${st.startDate}</small>`:''}</b></div>
        ${netDep!==0?`<div><span>Net deposits/withdrawals</span><b>${money(netDep)}</b></div>`:''}
        ${tr.length?`<div><span>Profit factor</span><b>${pf===Infinity?'∞':pf!=null?pf.toFixed(2):'—'} <small style="color:#7d827d">won per $1 lost</small></b></div>
        <div><span>Best / worst trade</span><b><span style="color:#69f0ae">${money(best)}</span> / <span style="color:#ff8a80">${money(worst)}</span></b></div>`:''}
      </div>
      <div class="ensMeta" style="margin-top:6px">${scan?`Last scan: <b>${scan.date}</b>${scan.late?' (late catch-up)':''} &nbsp; ${scanLine} · <small style="color:#7d827d">regime</small> <b style="color:#7fb2e0">${BOT_REGIME_NAMES[curReg]||curReg}</b>`:'No scan yet.'}
        · Next: <b>${nrTxt}</b> ${isExt?'<small style="color:#5f6b5f">(automatic · exits &amp; pending orders watched hourly)</small>':'<small style="color:#ffb3aa">(open this page in the morning — as a plain file it can’t wake itself)</small>'}
        <span class="ig" data-act="tip" data-tip="Cada manana (8:30am) el bot estudia BTC y ETH, 10 senales votan, abre trades de papel y deja ordenes pendientes (compra el retroceso / sigue la ruptura) que un vigilante revisa cada hora. El riesgo total abierto nunca pasa del 6% del capital. No usa dinero real.">ⓘ</span></div>
      ${posHtml}
      ${pendHtml?`<div class="trList"><div class="trListLbl">ARMED ORDERS · open if price touches the trigger</div>${pendHtml}</div>`:''}
      ${newsHtml}
      <div class="ensBd"><div class="ensBdTitle">Setups — which trade types are working <span class="ig" data-act="tip" data-tip="Ganados/total por tipo de entrada. Si un setup pierde en promedio tras 8 trades se le recorta el tamano a la mitad; tras 12, se desactiva solo.">ⓘ</span></div>
        <div class="ensBdRows">${setupHtml}</div>
      </div>
      <div class="ensBd"><div class="ensBdTitle">What it has learned — weight per signal <span class="ig" data-act="tip" data-tip="Cada senal gana peso cuando acierta y pierde peso cuando falla, con memoria reciente: lo de este mes pesa mas que lo del ano pasado.">ⓘ</span></div>
        <div class="ensBdRows">${wRows}</div>
        ${st.pretrain?`<div class="ensBdNote">Pre-trained on ${st.pretrain.days} days of history (signal hit-rate ${st.pretrain.hitRate}%). Bot instance created <b>${new Date(st.createdAt||Date.now()).toLocaleDateString(undefined,{month:'short',day:'numeric'})}</b> — if this date looks new, this device is running a fresh bot (use 📥 Restore with a backup to bring your trained one).</div>`:''}
        ${studyHtml}
      </div>
      ${activity?`<div class="trList"><div class="trListLbl">ACTIVITY · everything the bot did, with P&amp;L</div><div style="max-height:240px;overflow-y:auto">${activity}</div></div>`:''}
      ${lessons?`<div class="trList"><div class="trListLbl">RECENT LESSONS</div>${lessons}</div>`:''}
      ${jrows?`<div class="trList"><div class="trListLbl">BOT JOURNAL · ${tr.length} closed · ${winRate!=null?winRate+'% wins':''} · realized ${money(realized)}</div><div style="${botJournalAll?'max-height:360px;overflow-y:auto':''}">${jrows}</div>${tr.length>12?`<button class="bigBtn" style="width:100%;margin-top:7px" data-act="botjournal">${botJournalAll?'Show recent only':'Show ALL '+tr.length+' trades'}</button>`:''}</div>`:`<div class="paperEmpty">No closed trades yet — the journal fills in as the bot's calls play out.</div>`}
      <div class="paperBtns" style="flex-wrap:wrap"><button class="logBtn" data-act="botdeposit">💵 Add funds</button><button class="logBtn ghost" data-act="botwithdraw">Withdraw</button><button class="logBtn ghost" data-act="botbackup">🗂 Backup</button><button class="logBtn ghost" data-act="botrestore">📥 Restore</button><button class="logBtn ghost" data-act="botexport">⬇ CSV</button><button class="logBtn ghost" data-act="botreset">Reset</button></div>
      <div class="paperNote">Paper trading only — it never places real orders. BTC + ETH; entries from the morning scan plus armed dip/breakout orders filled hourly. Per trade: stop 1.6×ATR, 50% off at T1, breakeven + 2×ATR trail to the final target (3.2×ATR), max 10 days, ~0.2% fee, risk ~1–2% of equity each, total open risk capped at ${BOT_RISK_BUDGET}%.</div>
    </div>`;
}

/* compact always-visible bot status strip shown at the very top of the page */
function botStrip(){
  if(!botState)return '';
  const st=botState;
  const startEq=st.startEquity||10000;
  const realized=st.equity-startEq-(st.netDeposits||0);
  let unreal=0;(st.positions||[]).forEach(o=>{
    const ref=(st.lastPx&&st.lastPx[o.sym])||o.entry;
    const leg=p=>(o.dir===1?(p-o.entry)/o.entry:(o.entry-p)/o.entry)*100;
    const pct=o.scaled?0.5*leg(o.t1)+0.5*leg(ref):leg(ref);
    unreal+=st.equity*(pct/100)*(o.sizePct/100);});
  const tot=realized+unreal;
  const col=tot>0.005?'#00e676':tot<-0.005?'#ff1744':'#ffb300';
  const money=v=>(v<0?'−$':'+$')+Math.abs(v).toLocaleString('en-US',{maximumFractionDigits:Math.abs(v)<100?2:0});
  const n=(st.positions||[]).length, pend=(st.pending||[]).length;
  return `<div class="regime" style="border-color:#2a5d8e;background:linear-gradient(180deg,rgba(41,121,255,.08),rgba(41,121,255,.02))">
    <div class="regDot" style="background:${col}"></div>
    <div style="flex:1"><div class="regT" style="color:#7fb2e0">🤖 BOT · P&amp;L <span style="color:${col}">${money(tot)}</span> · ${n} open · ${pend} armed</div>
    <div class="regN">${(st.positions||[]).map(p=>p.sym+(p.dir===1?' ▲':' ▼')+p.sizePct+'%').join(' · ')||'no open trades'} · next scan ${botNextRun(new Date()).toLocaleTimeString([],{hour:'2-digit',minute:'2-digit'})}</div></div></div>`;
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
    ${botStrip()}
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
      try{const r=await botRunMorning({force:true});botState=r.state||await botLoad();botSetBadge(botState);}catch(err){}
      botBusy=false;if(store[sel])render(); break;}
    case "botexport": {if(!botState||!botState.trades.length)break;
      let pe=botState.startEquity||10000;
      downloadCSV([["opened","closed","asset","setup","direction","size_pct","entry","exit","return_pct","pnl_usd","exit_reason","equity_after"]]
        .concat(botState.trades.map(t=>{const dl=(t.eqAfter-pe).toFixed(2);pe=t.eqAfter;
          return [t.date,new Date(t.exitT).toISOString().slice(0,10),t.sym||"BTC",t.setup||"morning",t.dir===1?"LONG":"SHORT",t.sizePct,t.entry,t.exit,t.ret,dl,t.reason,t.eqAfter];})),"morning-bot-journal.csv"); break;}
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
          if(!obj||obj.startEquity==null||(!obj.weightsR&&!obj.weights))throw 0;
          if(typeof confirm==="function"&&!confirm("Replace the bot's current data with this backup?"))return;
          await botSave(botMigrate(obj));botState=await botLoad();botSetBadge(botState);if(store[sel])render();
          alert("Backup restored ✓");
        }catch(e){alert("That file doesn't look like a valid BTC Pro backup.");}};
      inp.click();break;}
    case "botreset": {if(typeof confirm==="function"&&!confirm("Reset the bot? This erases its paper record and re-learns from history."))break;
      botBusy=true;if(store[sel])render();
      try{await botSave(botDefaultState());botState=await botPretrain();botSetBadge(botState);}catch(err){botState=await botLoad();}
      botBusy=false;if(store[sel])render(); break;}
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
    if(!botState)botState=await botEnsureReady();           // first ever open: pre-trains on history
    if(botNeedsRun(botState)){                              // morning catch-up if the alarm was missed
      try{const r=await botRunMorning({});if(r.state)botState=r.state;}catch(e){}
    }
    if(botState&&botState.open){                            // manage stop/targets while the page is open
      try{const r=await botCheckExits();if(r.state)botState=r.state;}catch(e){}
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
