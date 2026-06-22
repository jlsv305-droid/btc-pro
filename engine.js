/* ============================================================================
   engine.js — shared, UI-free logic.
   Loaded by BOTH the app page (index.html) and the background service worker
   (bg.js via importScripts). Must never touch `document` or `window`.
   ============================================================================ */

/* ============================ INDICADORES ============================ */
const last=a=>a[a.length-1];
function clamp(x){return Math.max(-1,Math.min(1,x));}
function ema(v,p){const k=2/(p+1);const o=Array(v.length).fill(null);let pr=null;
  for(let i=0;i<v.length;i++){if(i<p-1)continue;if(pr===null){let s=0;for(let j=i-p+1;j<=i;j++)s+=v[j];pr=s/p;}else pr=v[i]*k+pr*(1-k);o[i]=pr;}return o;}
function rsiArr(c,p=14){const o=Array(c.length).fill(null);let g=0,l=0;
  for(let i=1;i<c.length;i++){const ch=c[i]-c[i-1],gg=Math.max(ch,0),ll=Math.max(-ch,0);
    if(i<=p){g+=gg;l+=ll;if(i===p){g/=p;l/=p;o[i]=l===0?100:100-100/(1+g/l);}}
    else{g=(g*(p-1)+gg)/p;l=(l*(p-1)+ll)/p;o[i]=l===0?100:100-100/(1+g/l);}}return o;}
function macdArr(c){const f=ema(c,12),s=ema(c,26);const m=c.map((_,i)=>f[i]!=null&&s[i]!=null?f[i]-s[i]:null);
  const v=m.map(x=>x==null?0:x);const fi=m.findIndex(x=>x!=null);
  const sig=ema(v,9).map((x,i)=>i>=fi+8?x:null);const h=m.map((x,i)=>x!=null&&sig[i]!=null?x-sig[i]:null);return{m,sig,h};}
function boll(c,p=20,k=2){const mid=[],up=[],lo=[];for(let i=0;i<c.length;i++){if(i<p-1){mid.push(null);up.push(null);lo.push(null);continue;}
  let m=0;for(let j=i-p+1;j<=i;j++)m+=c[j];m/=p;let v=0;for(let j=i-p+1;j<=i;j++)v+=(c[j]-m)**2;const sd=Math.sqrt(v/p);
  mid.push(m);up.push(m+k*sd);lo.push(m-k*sd);}return{mid,up,lo};}
function stochRsi(c,p=14){const r=rsiArr(c,p);const o=Array(c.length).fill(null);
  for(let i=0;i<r.length;i++){if(r[i]==null)continue;let hh=-1e18,ll=1e18,ok=true;
    for(let j=i-p+1;j<=i;j++){if(j<0||r[j]==null){ok=false;break;}hh=Math.max(hh,r[j]);ll=Math.min(ll,r[j]);}
    if(ok)o[i]=hh===ll?50:((r[i]-ll)/(hh-ll))*100;}return o;}
function williamsR(h,l,c,p=14){const o=Array(c.length).fill(null);for(let i=0;i<c.length;i++){if(i<p-1)continue;
  let hh=-1e18,ll=1e18;for(let j=i-p+1;j<=i;j++){hh=Math.max(hh,h[j]);ll=Math.min(ll,l[j]);}
  o[i]=hh===ll?-50:((hh-c[i])/(hh-ll))*-100;}return o;}
function roc(c,n=12){const o=Array(c.length).fill(null);for(let i=n;i<c.length;i++)o[i]=(c[i]/c[i-n]-1)*100;return o;}
function obv(c,v){const o=[0];for(let i=1;i<c.length;i++)o.push(o[i-1]+(c[i]>c[i-1]?v[i]:c[i]<c[i-1]?-v[i]:0));return o;}
function atrArr(h,l,c,p=14){const tr=[0];for(let i=1;i<c.length;i++){const a=h[i]-l[i],b=Math.abs(h[i]-c[i-1]),d=Math.abs(l[i]-c[i-1]);tr.push(Math.max(a,b,d));}
  const o=Array(c.length).fill(null);if(c.length<=p)return o;let s=0;for(let i=1;i<=p;i++)s+=tr[i];o[p]=s/p;
  for(let i=p+1;i<c.length;i++)o[i]=(o[i-1]*(p-1)+tr[i])/p;return o;}
function adxArr(h,l,c,p=14){const len=c.length;const pdm=[0],ndm=[0],tr=[0];
  for(let i=1;i<len;i++){const up=h[i]-h[i-1],dn=l[i-1]-l[i];pdm.push(up>dn&&up>0?up:0);ndm.push(dn>up&&dn>0?dn:0);
    tr.push(Math.max(h[i]-l[i],Math.abs(h[i]-c[i-1]),Math.abs(l[i]-c[i-1])));}
  let str=0,sp=0,sn=0;for(let i=1;i<=p;i++){str+=tr[i];sp+=pdm[i];sn+=ndm[i];}
  const pdi=Array(len).fill(null),ndi=Array(len).fill(null),dx=Array(len).fill(null);
  for(let i=p;i<len;i++){if(i>p){str=str-str/p+tr[i];sp=sp-sp/p+pdm[i];sn=sn-sn/p+ndm[i];}
    const dp=str===0?0:100*sp/str,dn=str===0?0:100*sn/str;pdi[i]=dp;ndi[i]=dn;
    dx[i]=(dp+dn)===0?0:100*Math.abs(dp-dn)/(dp+dn);}
  const adx=Array(len).fill(null);let s=0,cnt=0;
  for(let i=p;i<len&&cnt<p;i++){if(dx[i]!=null){s+=dx[i];cnt++;}if(cnt===p)adx[i]=s/p;}
  let started=adx.findIndex(x=>x!=null);
  for(let i=started+1;i<len;i++)if(dx[i]!=null&&adx[i-1]!=null)adx[i]=(adx[i-1]*(p-1)+dx[i])/p;
  return{adx,pdi,ndi};}
function supertrend(h,l,c,period=10,mult=3){
  const atr=atrArr(h,l,c,period);const n=c.length;
  const ub=Array(n).fill(null),lb=Array(n).fill(null),st=Array(n).fill(null),dir=Array(n).fill(null);
  let started=false;
  for(let i=0;i<n;i++){
    if(atr[i]==null)continue;
    const hl2=(h[i]+l[i])/2, ubB=hl2+mult*atr[i], lbB=hl2-mult*atr[i];
    if(!started){ub[i]=ubB;lb[i]=lbB;st[i]=ubB;dir[i]=-1;started=true;continue;}
    ub[i]=(ubB<ub[i-1]||c[i-1]>ub[i-1])?ubB:ub[i-1];
    lb[i]=(lbB>lb[i-1]||c[i-1]<lb[i-1])?lbB:lb[i-1];
    if(st[i-1]===ub[i-1]) st[i]=c[i]<=ub[i]?ub[i]:lb[i];
    else st[i]=c[i]>=lb[i]?lb[i]:ub[i];
    dir[i]=st[i]===ub[i]?-1:1;
  }
  return{line:st,dir};
}
function smaLast(a,p){const v=a.filter(x=>x!=null);if(v.length<p)return null;let s=0;for(let i=v.length-p;i<v.length;i++)s+=v[i];return s/p;}
function levels(c,look=4){const piv=[];for(let i=look;i<c.length-look;i++){let hi=true,lo=true;
  for(let j=i-look;j<=i+look;j++){if(c[j]>c[i])hi=false;if(c[j]<c[i])lo=false;}
  if(hi)piv.push({t:'res',p:c[i]});if(lo)piv.push({t:'sup',p:c[i]});}
  const price=last(c);const res=piv.filter(x=>x.t==='res'&&x.p>price*1.001).map(x=>x.p).sort((a,b)=>a-b);
  const sup=piv.filter(x=>x.t==='sup'&&x.p<price*0.999).map(x=>x.p).sort((a,b)=>b-a);
  const uniq=arr=>{const o=[];for(const v of arr){if(!o.some(x=>Math.abs(x-v)/v<0.012))o.push(v);}return o;};
  return{res:uniq(res).slice(0,2),sup:uniq(sup).slice(0,2)};}

/* ============================ SEÑALES ============================ */
function computeAll(S){
  const {h,l,c,v}=S, i=c.length-1;
  const RSI=rsiArr(c), {m:MACD,sig:SIG,h:HIST}=macdArr(c);
  const E20=ema(c,20),E50=ema(c,50),E200=ema(c,200);
  const BB=boll(c), SR=stochRsi(c), WR=williamsR(h,l,c), RC=roc(c), OB=obv(c,v), AT=atrArr(h,l,c);
  const {adx:ADX,pdi:PDI,ndi:NDI}=adxArr(h,l,c);
  const ST=supertrend(h,l,c,10,3);
  const price=c[i], cards=[];

  let s=0,st="Neutral";const rsi=RSI[i];
  if(rsi<30){s=1;st="Oversold";}else if(rsi<42){s=.5;st="Weak";}else if(rsi>70){s=-1;st="Overbought";}else if(rsi>58){s=-.5;st="Hot";}
  cards.push({g:"Momentum",n:"RSI (14)",val:rsi.toFixed(1),st,score:s,note:s>0?"Possible bounce":s<0?"Possible pullback":"No extremes"});

  let s2=0,st2="Neutral";const sr=SR[i];
  if(sr<15){s2=1;st2="Oversold";}else if(sr<30){s2=.5;st2="Low";}else if(sr>85){s2=-1;st2="Overbought";}else if(sr>70){s2=-.5;st2="High";}
  cards.push({g:"Momentum",n:"Stoch RSI",val:sr.toFixed(0),st:st2,score:s2,note:s2>0?"Upturn near":s2<0?"Downturn near":"Neutral"});

  let s3=0,st3="Neutral";const wr=WR[i];
  if(wr<-80){s3=.8;st3="Oversold";}else if(wr>-20){s3=-.8;st3="Overbought";}
  cards.push({g:"Momentum",n:"Williams %R*",val:wr.toFixed(0),st:st3,score:s3,note:s3>0?"Buy zone":s3<0?"Sell zone":"Mid-range"});

  let s4=0,st4="Flat";const rc=RC[i];
  if(rc>3){s4=.6;st4="Accelerating";}else if(rc>0.5){s4=.3;st4="Positive";}else if(rc<-3){s4=-.6;st4="Falling";}else if(rc<-0.5){s4=-.3;st4="Negative";}
  cards.push({g:"Momentum",n:"ROC (12)",val:rc.toFixed(1)+"%",st:st4,score:s4,note:"Recent price change"});

  const sd=ST.dir[i], flipped=ST.dir[i]!==ST.dir[i-1];
  let s5=sd===1?0.9:-0.9; if(flipped)s5=sd;
  cards.push({g:"Trend",n:"Supertrend (10,3)*",val:sd===1?"Bullish":"Bearish",
    st:flipped?(sd===1?"⟳ Bull flip":"⟳ Bear flip"):(sd===1?"Buy active":"Sell active"),
    score:clamp(s5),note:"Line "+(sd===1?"below price":"above price")});

  let s6=0;if(price>E20[i])s6+=.3;else s6-=.3;
  const haveLT=E200[i]!=null;
  if(haveLT){if(price>E200[i])s6+=.4;else s6-=.4;}
  const gc=(E50[i]!=null&&haveLT)?E50[i]>E200[i]:(price>E50[i]);
  s6+=gc?.3:-.3;
  cards.push({g:"Trend",n:haveLT?"EMA 20/50/200":"EMA 20/50",val:gc?"Golden":"Death",st:gc?"Bullish":"Bearish",score:clamp(s6),
    note:haveLT?("Price "+(price>E200[i]?"above":"below")+" EMA200"):("Price "+(price>E50[i]?"above":"below")+" EMA50")});

  let s7=0,st7="Neutral";if(MACD[i]>SIG[i]){s7+=.5;st7="Bullish cross";}else{s7-=.5;st7="Bearish cross";}
  if(HIST[i]!=null&&HIST[i-1]!=null){if(HIST[i]>HIST[i-1])s7+=.5;else s7-=.5;}
  cards.push({g:"Trend",n:"MACD",val:Math.round(MACD[i]),st:st7,score:clamp(s7),note:HIST[i]>0?"Positive histogram":"Negative histogram"});

  const adx=ADX[i]||0,dir=PDI[i]>NDI[i]?1:-1;
  let s8=clamp(dir*Math.min(adx/35,1)*0.9),st8;
  if(adx<20){st8="No trend";s8*=0.3;}else if(adx<40)st8=(dir>0?"Uptrend":"Downtrend");else st8=(dir>0?"Strong up":"Strong down");
  cards.push({g:"Trend",n:"ADX (14)*",val:adx.toFixed(0),st:st8,score:s8,note:adx<20?"Range / sideways":"Trend "+(dir>0?"+":"−")});

  const pb=BB.up[i]===BB.lo[i]?.5:(price-BB.lo[i])/(BB.up[i]-BB.lo[i]);
  let s9=0,st9="Inside";if(pb<.08){s9=1;st9="Lower band";}else if(pb<.25){s9=.5;st9="Near lower";}else if(pb>.92){s9=-1;st9="Upper band";}else if(pb>.75){s9=-.5;st9="Near upper";}
  cards.push({g:"Volatility",n:"Bollinger %B",val:Math.round(pb*100)+"%",st:st9,score:s9,note:s9>0?"Short-term oversold":s9<0?"Short-term overbought":"Normal"});

  const atrPct=(AT[i]/price)*100;
  cards.push({g:"Volatility",n:"Volatility (ATR%)*",val:atrPct.toFixed(1)+"%",st:atrPct>4?"High":atrPct>2?"Medium":"Low",score:0,note:"Risk / stop size"});

  const obvSma=smaLast(OB.slice(0,i+1),20);let s11=0,st11="Flat";
  if(obvSma!=null){if(OB[i]>obvSma){s11=.7;st11="Accumulation";}else if(OB[i]<obvSma){s11=-.7;st11="Distribution";}}
  cards.push({g:"Volume",n:"OBV",val:OB[i]>obvSma?"↑":"↓",st:st11,score:s11,note:s11>0?"Volume backs upside":s11<0?"Volume backs downside":"No bias"});

  const volAvg=smaLast(v.slice(0,i+1),20)||v[i];const vr=v[i]/volAvg;
  cards.push({g:"Volume",n:"Rel. volume",val:vr.toFixed(1)+"x",st:vr>1.5?"Elevated":vr<0.6?"Low":"Normal",score:0,note:"vs 20-bar avg"});

  const dirCards=cards.filter(x=>!["Volatility (ATR%)*","Rel. volume"].includes(x.n));
  const total=dirCards.reduce((a,x)=>a+x.score,0);const norm=clamp(total/dirCards.length/0.62);
  const agree=dirCards.filter(x=>Math.sign(x.score)===Math.sign(norm)&&x.score!==0).length;

  let verdict,col,ic;
  if(norm>.4){verdict="STRONG BUY";col="#00e676";ic="↑";}
  else if(norm>.15){verdict="BUY";col="#69f0ae";ic="↑";}
  else if(norm<-.4){verdict="STRONG SELL";col="#ff1744";ic="↓";}
  else if(norm<-.15){verdict="SELL";col="#ff8a80";ic="↓";}
  else{verdict="NEUTRAL / WAIT";col="#ffb300";ic="—";}

  const chart=[];const n=c.length;const start=Math.max(0,n-120);
  for(let j=start;j<n;j++)chart.push({price:c[j],o:(j>0?c[j-1]:c[j]),h:h[j],l:l[j],e20:E20[j],e50:E50[j],e200:E200[j],up:BB.up[j],lo:BB.lo[j],
    vol:v[j],upBar:c[j]>=(c[j-1]??c[j]),st:ST.line[j],stDir:ST.dir[j]});
  return{price,cards,norm,verdict,col,ic,agree,total:dirCards.length,chart,atrPct,levels:levels(c)};
}

function signalNormSeries(S){
  const {h,l,c,v}=S, n=c.length;
  const RSI=rsiArr(c), MM=macdArr(c), MACD=MM.m, SIG=MM.sig, HIST=MM.h,
    E20=ema(c,20),E50=ema(c,50),E200=ema(c,200),
    BB=boll(c), SR=stochRsi(c), WR=williamsR(h,l,c), RC=roc(c), OB=obv(c,v),
    AD=adxArr(h,l,c), ADX=AD.adx, PDI=AD.pdi, NDI=AD.ndi, ST=supertrend(h,l,c,10,3);
  const OBS=Array(n).fill(null);
  for(let i=0;i<n;i++){if(i>=19){let s=0;for(let k=i-19;k<=i;k++)s+=OB[k];OBS[i]=s/20;}}
  const norm=Array(n).fill(null), conf=Array(n).fill(null);
  for(let i=1;i<n;i++){
    if(RSI[i]==null||SIG[i]==null||E50[i]==null||BB.up[i]==null||SR[i]==null||ADX[i]==null||
       ST.dir[i]==null||ST.dir[i-1]==null||HIST[i]==null||HIST[i-1]==null||OBS[i]==null||WR[i]==null||RC[i]==null)continue;
    const price=c[i]; const arr=[];
    let s=0;const rsi=RSI[i];if(rsi<30)s=1;else if(rsi<42)s=.5;else if(rsi>70)s=-1;else if(rsi>58)s=-.5;arr.push(s);
    let s2=0;const sr=SR[i];if(sr<15)s2=1;else if(sr<30)s2=.5;else if(sr>85)s2=-1;else if(sr>70)s2=-.5;arr.push(s2);
    let s3=0;const wr=WR[i];if(wr<-80)s3=.8;else if(wr>-20)s3=-.8;arr.push(s3);
    let s4=0;const rc=RC[i];if(rc>3)s4=.6;else if(rc>0.5)s4=.3;else if(rc<-3)s4=-.6;else if(rc<-0.5)s4=-.3;arr.push(s4);
    const sd=ST.dir[i],flip=ST.dir[i]!==ST.dir[i-1];let s5=sd===1?0.9:-0.9;if(flip)s5=sd;arr.push(clamp(s5));
    let s6=0;if(price>E20[i])s6+=.3;else s6-=.3;const hL=E200[i]!=null;if(hL){if(price>E200[i])s6+=.4;else s6-=.4;}
    const gc=(E50[i]!=null&&hL)?E50[i]>E200[i]:(price>E50[i]);s6+=gc?.3:-.3;arr.push(clamp(s6));
    let s7=0;if(MACD[i]>SIG[i])s7+=.5;else s7-=.5;if(HIST[i]>HIST[i-1])s7+=.5;else s7-=.5;arr.push(clamp(s7));
    const adx=ADX[i]||0,dir=PDI[i]>NDI[i]?1:-1;let s8=clamp(dir*Math.min(adx/35,1)*0.9);if(adx<20)s8*=0.3;arr.push(s8);
    const pb=BB.up[i]===BB.lo[i]?.5:(price-BB.lo[i])/(BB.up[i]-BB.lo[i]);let s9=0;if(pb<.08)s9=1;else if(pb<.25)s9=.5;else if(pb>.92)s9=-1;else if(pb>.75)s9=-.5;arr.push(s9);
    let s11=0;if(OB[i]>OBS[i])s11=.7;else if(OB[i]<OBS[i])s11=-.7;arr.push(s11);
    const nm=clamp(arr.reduce((a,b)=>a+b,0)/arr.length/0.62); norm[i]=nm;
    const ag=arr.filter(x=>x!==0&&Math.sign(x)===Math.sign(nm)).length;
    conf[i]=Math.max(1,Math.min(10,Math.round((Math.abs(nm)*0.6+(ag/arr.length)*0.4)*10)));
  }
  return {norm,conf,stDir:ST.dir,e200:E200,stLine:ST.line};
}
function backtest(series,S,th,strat,fromIdx,stopPct,allowShort){
  fromIdx=fromIdx||0;
  const {norm,conf,stDir,e200}=series, closes=S.c; let pos=null; const trades=[];
  let eqC=1, peak=1, maxDD=0;
  const COST=0.2; /* round-trip fee+slippage % charged on every closed trade */
  const close=(p,exit,j,stopped)=>{const ret=(p.dir===1?(exit-p.entry)/p.entry*100:(p.entry-exit)/p.entry*100)-COST;
    const mfe=p.dir===1?(p.maxH-p.entry)/p.entry*100:(p.entry-p.minL)/p.entry*100;
    const mae=p.dir===1?(p.minL-p.entry)/p.entry*100:(p.entry-p.maxH)/p.entry*100;
    trades.push({dir:p.dir,inIdx:p.inIdx,outIdx:j,entry:p.entry,exit,ret,conf:p.conf,stop:p.stop,stopped,mfe,mae});eqC*=(1+ret/100);};
  const mkStop=(dir,entry)=>!stopPct?0:(dir===1?entry*(1-stopPct/100):entry*(1+stopPct/100));
  for(let j=1;j<closes.length;j++){
    let up=false,dn=false;
    if(strat==='signal'){ if(norm[j]==null||conf[j]==null)continue;
      up=norm[j]>0.15&&(conf[j]>=th); dn=norm[j]<-0.15;
    } else { if(stDir[j]==null||stDir[j-1]==null)continue;
      up=stDir[j]===1&&stDir[j-1]===-1; dn=stDir[j]===-1&&stDir[j-1]===1;
      if(strat==='sttrend')up=up&&(e200[j]==null||closes[j]>e200[j]);
    }
    if(pos){ if(S.h[j]>pos.maxH)pos.maxH=S.h[j]; if(S.l[j]<pos.minL)pos.minL=S.l[j];
      if(pos.dir===1&&pos.stop&&S.l[j]<=pos.stop){close(pos,pos.stop,j,true);pos=null;}
      else if(pos.dir===-1&&pos.stop&&S.h[j]>=pos.stop){close(pos,pos.stop,j,true);pos=null;}
    }
    if(pos){ if(pos.dir===1&&dn){close(pos,closes[j],j,false);pos=null;}
      else if(pos.dir===-1&&up){close(pos,closes[j],j,false);pos=null;} }
    if(!pos&&j>=fromIdx){
      if(up){pos={dir:1,inIdx:j,entry:closes[j],conf:conf[j]||0,maxH:S.h[j],minL:S.l[j],stop:mkStop(1,closes[j])};}
      else if(dn&&allowShort&&strat!=='sttrend'&&(e200[j]==null||closes[j]<e200[j])){pos={dir:-1,inIdx:j,entry:closes[j],conf:conf[j]||0,maxH:S.h[j],minL:S.l[j],stop:mkStop(-1,closes[j])};}
    }
    if(j>=fromIdx){ const u=pos?(pos.dir===1?(closes[j]-pos.entry)/pos.entry:(pos.entry-closes[j])/pos.entry):0;
      const ce=eqC*(1+u); if(ce>peak)peak=ce; const dd=(ce-peak)/peak*100; if(dd<maxDD)maxDD=dd; }
  }
  let openTrade=null;
  if(pos){const L=closes.length-1; if(S.h[L]>pos.maxH)pos.maxH=S.h[L]; if(S.l[L]<pos.minL)pos.minL=S.l[L];
    const ret=pos.dir===1?(closes[L]-pos.entry)/pos.entry*100:(pos.entry-closes[L])/pos.entry*100;
    const mfe=pos.dir===1?(pos.maxH-pos.entry)/pos.entry*100:(pos.entry-pos.minL)/pos.entry*100;
    const mae=pos.dir===1?(pos.minL-pos.entry)/pos.entry*100:(pos.entry-pos.maxH)/pos.entry*100;
    openTrade={dir:pos.dir,inIdx:pos.inIdx,entry:pos.entry,cur:closes[L],ret,conf:pos.conf,stop:pos.stop,mfe,mae};}
  const total=(eqC-1)*100;
  const W=trades.filter(t=>t.ret>0), L=trades.filter(t=>t.ret<=0);
  const avgWin=W.length?W.reduce((a,t)=>a+t.ret,0)/W.length:0;
  const avgLoss=L.length?L.reduce((a,t)=>a+t.ret,0)/L.length:0;
  const gW=W.reduce((a,t)=>a+t.ret,0), gL=Math.abs(L.reduce((a,t)=>a+t.ret,0));
  const pf=gL>0?gW/gL:(gW>0?Infinity:0);
  return {trades,openTrade,total,maxDD,wins:W.length,winRate:trades.length?W.length/trades.length*100:0,avgWin,avgLoss,pf};
}
function holdStats(c,from){
  from=from||0; const base=c[from]; if(!base)return{ret:0,maxDD:0};
  let peak=base,maxDD=0;
  for(let i=from;i<c.length;i++){ if(c[i]>peak)peak=c[i]; const dd=(c[i]-peak)/peak*100; if(dd<maxDD)maxDD=dd; }
  return {ret:(c[c.length-1]-base)/base*100, maxDD};
}

/* ================= ENSEMBLE (probabilistic, risk-managed) ================= */
function _emean(a){return a.length?a.reduce((x,y)=>x+y,0)/a.length:0;}
function _estd(a){if(a.length<2)return 0;const m=_emean(a);return Math.sqrt(a.reduce((x,y)=>x+(y-m)*(y-m),0)/(a.length-1));}
function _emed(a){const b=a.filter(x=>x!=null&&isFinite(x)).slice().sort((x,y)=>x-y);return b.length?b[Math.floor(b.length/2)]:0;}
function ensembleBuild(S){
  const c=S.c,h=S.h,l=S.l,n=c.length;
  const sig=signalNormSeries(S);
  const E50=ema(c,50),MM=macdArr(c),HIST=MM.h,AD=adxArr(h,l,c),ADX=AD.adx,atr=atrArr(h,l,c);
  const wk=resampleSeries(S,7),wkE=ema(wk.c,30);
  const wkTrend=wk.c.map((cc,i)=>wkE[i]!=null?Math.sign(cc-wkE[i]):0);
  const weeklyAt=ts=>{let r=0;for(let i=0;i<wk.t.length;i++){if(wk.t[i]<=ts)r=wkTrend[i];else break;}return r;};
  const comps=i=>{const d1=sig.stDir[i],d2=sig.e200[i]!=null?Math.sign(c[i]-sig.e200[i]):null,d3=sig.norm[i],d4=(E50[i]!=null&&sig.e200[i]!=null)?Math.sign(E50[i]-sig.e200[i]):null,d5=HIST[i]!=null?Math.sign(HIST[i]):null;return[d1,d2,d3,d4,d5];};
  const isEnd=Math.max(250,Math.floor(n*0.65));
  const hit=[0,0,0,0,0],tot=[0,0,0,0,0];
  for(let i=210;i<isEnd-1;i++){const cs=comps(i),fr=Math.sign(c[i+1]-c[i]);if(fr===0)continue;for(let k=0;k<5;k++){const d=cs[k];if(d==null||d===0)continue;tot[k]++;if(Math.sign(d)===fr)hit[k]++;}}
  let W=hit.map((hh,k)=>tot[k]>30?Math.max(0,2*(hh/tot[k])-1):0);
  if(W.reduce((a,b)=>a+b,0)===0)W=[1,1,1,1,1];
  const medVol=_emed(atr.slice(0,isEnd).map((a,i)=>a!=null?a/c[i]:null))||0.03;
  const e=Array(n).fill(0),P=Array(n).fill(0.5);
  for(let i=0;i<n;i++){if(sig.stDir[i]==null||sig.e200[i]==null||sig.norm[i]==null){e[i]=0;P[i]=0.5;continue;}const cs=comps(i);let sw=0,ws=0;for(let k=0;k<5;k++){if(cs[k]==null)continue;sw+=W[k]*cs[k];ws+=W[k];}const Sc=ws>0?sw/ws:0;const adxG=Math.max(0.3,Math.min(1,(ADX[i]||0)/25));const p=1/(1+Math.exp(-3*Sc*adxG));P[i]=p;let ex=Math.max(0,Math.min(1,(p-0.5)*2));const volPct=(atr[i]||medVol*c[i])/c[i];ex*=Math.max(0.3,Math.min(1.3,medVol/volPct));if(weeklyAt(S.t[i])<0)ex*=0.35;e[i]=Math.max(0,Math.min(1,ex));}
  const li=n-1, lc=comps(li);
  const names=['Supertrend','Above 200-day avg','12-indicator score','50 vs 200 trend','MACD momentum'];
  const breakdown=lc.map((d,k)=>({name:names[k],dir:d==null?0:(d>0?1:(d<0?-1:0)),w:+W[k].toFixed(2)}));
  return {e,P,W,weekly:weeklyAt(S.t[n-1]),breakdown,adx:ADX[li]||0};
}
function simSized(S,e,fromIdx,cost){const c=S.c,n=c.length;let eq=1,peak=1,maxDD=0;const rets=[];for(let i=fromIdx+1;i<n;i++){const r=(c[i]-c[i-1])/c[i-1];const net=(e[i-1]||0)*r-cost*Math.abs((e[i-1]||0)-(e[i-2]||0));eq*=(1+net);rets.push(net);if(eq>peak)peak=eq;const dd=(eq-peak)/peak;if(dd<maxDD)maxDD=dd;}const yrs=(S.t[n-1]-S.t[fromIdx])/31557600000;const cagr=yrs>0?(Math.pow(Math.max(eq,1e-9),1/yrs)-1)*100:0;const sharpe=_estd(rets)>0?_emean(rets)/_estd(rets)*Math.sqrt(365):0;return{total:(eq-1)*100,maxDD:maxDD*100,sharpe,cagr,mar:Math.abs(maxDD)>0?cagr/Math.abs(maxDD*100):0};}
function holdSharpe(c,t,fromIdx){let rets=[];for(let i=fromIdx+1;i<c.length;i++)rets.push((c[i]-c[i-1])/c[i-1]);return _estd(rets)>0?_emean(rets)/_estd(rets)*Math.sqrt(365):0;}
/* Valuation: where price sits vs its long-term power-law growth line (log price vs log time). */
function valuationZone(c){
  const n=c.length; if(n<200)return null;
  let sx=0,sy=0,sxx=0,sxy=0,m=0;
  for(let i=0;i<n;i++){if(c[i]<=0)continue;const x=Math.log(i+1),y=Math.log(c[i]);sx+=x;sy+=y;sxx+=x*x;sxy+=x*y;m++;}
  const b=(m*sxy-sx*sy)/(m*sxx-sx*sx), a=(sy-b*sx)/m;
  let ss=0,cnt=0;for(let i=0;i<n;i++){if(c[i]<=0)continue;const r=Math.log(c[i])-(a+b*Math.log(i+1));ss+=r*r;cnt++;}
  const sd=Math.sqrt(ss/cnt)||1, li=n-1, fitNow=a+b*Math.log(li+1);
  const z=(Math.log(c[li])-fitNow)/sd, line=Math.exp(fitNow), pct=(c[li]/line-1)*100;
  let label,color;
  if(z<-1.2){label='CHEAP — historically a good buy zone';color='#00e676';}
  else if(z<-0.4){label='Below trend — slightly cheap';color='#69f0ae';}
  else if(z<=0.4){label='Fair value — near its trend line';color='#ffb300';}
  else if(z<=1.2){label='Above trend — getting pricey';color='#ff8a80';}
  else {label='EXPENSIVE — historically risky';color='#ff1744';}
  return {z,pct,line,color,label,pos:Math.max(0,Math.min(1,(z+2.5)/5))};
}
/* Bounce odds: after a weekly drop like now, how often did the next week rise? */
function bounceStats(c){
  const rets=[];for(let i=1;i<c.length;i++)rets.push((c[i]-c[i-1])/c[i-1]);
  if(rets.length<12)return null;
  const cur=rets[rets.length-1];
  if(cur>=0)return {isDrop:false,cur:cur*100};
  let up=0,tot=0,sum=0;for(let i=0;i<rets.length-1;i++){if(rets[i]<=cur){tot++;if(rets[i+1]>0)up++;sum+=rets[i+1];}}
  return {isDrop:true,cur:cur*100,prob:tot?up/tot*100:null,avg:tot?sum/tot*100:null,n:tot};
}

/* ============================ DATOS ============================ */
const CG_IDS={BTC:'bitcoin',ETH:'ethereum'};
function resample(prices,vols,every){
  const c=prices.map(p=>p[1]),vv=vols.map(p=>p[1]),t=prices.map(p=>p[0]);
  if(every<=1)return {h:c.slice(),l:c.slice(),c,v:vv,t};
  const oc=[],oh=[],ol=[],ov=[],ot=[];
  for(let i=0;i<c.length;i+=every){const slc=c.slice(i,i+every);if(!slc.length)break;
    oc.push(slc[slc.length-1]);oh.push(Math.max(...slc));ol.push(Math.min(...slc));
    ov.push(vv.slice(i,i+every).reduce((a,b)=>a+b,0));ot.push(t[i]);}
  return{h:oh,l:ol,c:oc,v:ov,t:ot};
}
function resampleSeries(S,every){
  const n=S.c.length, c=[],h=[],l=[],v=[],t=[];
  if(!n)return{h,l,c,v,t};
  let dt=86400000; for(let i=1;i<Math.min(n,8);i++){const d=S.t[i]-S.t[i-1];if(d>0){dt=d;break;}}
  const period=every*dt;
  function push(a,b){const cs=S.c.slice(a,b);if(!cs.length)return;
    c.push(cs[cs.length-1]);h.push(Math.max(...S.h.slice(a,b)));l.push(Math.min(...S.l.slice(a,b)));
    v.push(S.v.slice(a,b).reduce((x,y)=>x+y,0));t.push(S.t[a]);}
  let key=Math.floor(S.t[0]/period), s=0;
  for(let i=1;i<n;i++){const k=Math.floor(S.t[i]/period);if(k!==key){push(s,i);key=k;s=i;}}
  push(s,n);
  return{h,l,c,v,t};}
async function fetchCG(sym,days){
  const r=await fetch("https://api.coingecko.com/api/v3/coins/"+(CG_IDS[sym]||'bitcoin')+"/market_chart?vs_currency=usd&days="+days);
  if(r.status===429)throw{rate:true};if(!r.ok)throw new Error();
  const j=await r.json();if(!j.prices||!j.prices.length)throw new Error();return j;
}
async function fetchBinance(sym,interval,limit){
  const r=await fetch("https://data-api.binance.vision/api/v3/klines?symbol="+sym+"USDT&interval="+interval+"&limit="+limit);
  if(!r.ok)throw new Error();const k=await r.json();
  return{h:k.map(x=>+x[2]),l:k.map(x=>+x[3]),c:k.map(x=>+x[4]),v:k.map(x=>+x[5]),t:k.map(x=>x[0])};
}
async function fetchSentiment(limit){
  try{const r=await fetch("https://api.alternative.me/fng/?limit="+(limit||30));if(!r.ok)throw 0;
    const j=await r.json();if(!j.data)throw 0;
    return j.data.map(d=>({v:+d.value,cls:d.value_classification,t:+d.timestamp*1000})).reverse();}catch(e){return null;}
}
/* Binance public data mirror: real OHLCV, no API key, CORS-friendly.
   Pages of up to 1000 candles are chained backwards to build deep history
   (BTC/ETH daily data reaches back to 2017 ≈ 9 years). */
async function fetchBinancePaged(sym,interval,totalBars){
  let out=[], endTime=Date.now(), guard=0;
  while(out.length<totalBars&&guard++<8){
    const lim=Math.min(1000,totalBars-out.length);
    const r=await fetch("https://data-api.binance.vision/api/v3/klines?symbol="+sym+"USDT&interval="+interval+"&limit="+lim+"&endTime="+endTime);
    if(!r.ok)break;
    const k=await r.json(); if(!Array.isArray(k)||!k.length)break;
    out=k.concat(out); endTime=k[0][0]-1;
    if(k.length<lim)break;
  }
  if(!out.length)throw new Error("binance-empty");
  const seen={},rows=[]; out.sort((a,b)=>a[0]-b[0]).forEach(x=>{if(!seen[x[0]]){seen[x[0]]=1;rows.push(x);}});
  return{h:rows.map(x=>+x[2]),l:rows.map(x=>+x[3]),c:rows.map(x=>+x[4]),v:rows.map(x=>+x[5]),t:rows.map(x=>x[0])};
}
/* Full 4-timeframe store for the UI: 0=12H 1=1D 2=3D 3=1W */
async function loadStoreFor(sym){
  try{
    const daily=await fetchBinancePaged(sym,"1d",4000);
    let hourly; try{hourly=await fetchBinancePaged(sym,"1h",3000);}catch(e){hourly=daily;}
    return {0:resampleSeries(hourly,12),1:daily,2:resampleSeries(daily,3),3:resampleSeries(daily,7)};
  }catch(e){}
  try{
    const j90=await fetchCG(sym,90); const hourly=resample(j90.prices,j90.total_volumes,1);
    let daily; try{const jw=await fetchCG(sym,1460);daily=resample(jw.prices,jw.total_volumes,1);}
    catch(e2){const j365=await fetchCG(sym,365);daily=resample(j365.prices,j365.total_volumes,1);}
    return {0:resampleSeries(hourly,12),1:daily,2:resampleSeries(daily,3),3:resampleSeries(daily,7)};
  }catch(e){}
  const h=await fetchBinance(sym,"1h",1000),d=await fetchBinance(sym,"1d",1000);
  return {0:resampleSeries(h,12),1:d,2:resampleSeries(d,3),3:resampleSeries(d,7)};
}
/* Lightweight daily-only load for the bot */
async function loadDailyFor(sym,days){
  try{return await fetchBinancePaged(sym,"1d",days||900);}catch(e){}
  try{const j=await fetchCG(sym,365);return resample(j.prices,j.total_volumes,1);}catch(e){}
  return await fetchBinance(sym,"1d",Math.min(days||900,1000));
}

/* ===========================================================================
   MORNING BOT v3 — paper trading only. Multi-position portfolio (BTC+ETH),
   pending orders, REGIME-AWARE learning (separate weights for bull/bear ×
   calm/volatile markets), a NEWS RADAR (headline sentiment & volatility risk
   from major crypto outlets) and a NIGHTLY STUDY that re-learns weights on
   fresh data and walk-forward-tests dozens of strategy variants, adopting a
   new one only if it wins out-of-sample. Never touches real money.
   =========================================================================== */
const BOT_ASSETS=['BTC','ETH'];
const BOT_REGIMES=['bullCalm','bullVol','bearCalm','bearVol'];
const BOT_REGIME_NAMES={bullCalm:'BULL · calm',bullVol:'BULL · volatile',bearCalm:'BEAR · calm',bearVol:'BEAR · volatile'};
const BOT_START_EQUITY=10000;
const BOT_COST=0.2;            // % round-trip fee+slippage per closed trade
const BOT_RUN_HOUR=8, BOT_RUN_MIN=30;     // morning scan
const BOT_NIGHT_HOUR=21, BOT_NIGHT_MIN=30; // nightly study
const BOT_MAX_HOLD=10;         // days
const BOT_PEND_TH=0.05;        // weaker lean still arms pending orders
const BOT_PEND_HOURS=48;       // pending orders expire after 2 days
const BOT_DIP_ATR=1.2;         // dip entry: 1.2×ATR pullback from scan price
const BOT_ETA=0.06;            // learning rate
const BOT_DECAY=0.97;          // recency: recent outcomes matter more
const BOT_W_MIN=0.15, BOT_W_MAX=3;
const BOT_TRAIL_ATR=2.0;       // fallback trail width
const BOT_RISK_MIN=1.0, BOT_RISK_MAX=2.0; // % equity at risk per trade
const BOT_RISK_BUDGET=6.0;     // max total % of equity at risk at once
const BOT_DEFAULT_PARAMS={th:0.12,stopATR:1.6,t2ATR:3.2,trailATR:2.0};
const BOT_SETUPS=[['morning','Morning signal'],['dip','Dip-buy limit'],['brk','Breakout stop']];
const BOT_SIGNALS=[
  {id:'st',    name:'Supertrend trend'},
  {id:'e200',  name:'Price vs 200-day'},
  {id:'comp',  name:'12-indicator composite'},
  {id:'cross', name:'50/200-day cross'},
  {id:'macd',  name:'MACD momentum'},
  {id:'brk',   name:'20-day breakout'},
  {id:'rsi2',  name:'RSI(2) dip-buy'},
  {id:'bbx',   name:'Bollinger extreme'},
  {id:'wk',    name:'Weekly trend'},
  {id:'fng',   name:'Fear&Greed contrarian'},
  {id:'news',  name:'News sentiment'}
];
function botPad(n){return (n<10?'0':'')+n;}
function botDayStr(d){return d.getFullYear()+'-'+botPad(d.getMonth()+1)+'-'+botPad(d.getDate());}
function botNextRun(now){
  const t=new Date(now.getFullYear(),now.getMonth(),now.getDate(),BOT_RUN_HOUR,BOT_RUN_MIN,0,0);
  if(t.getTime()<=now.getTime())t.setDate(t.getDate()+1);
  return t;
}
function botNextNight(now){
  const t=new Date(now.getFullYear(),now.getMonth(),now.getDate(),BOT_NIGHT_HOUR,BOT_NIGHT_MIN,0,0);
  if(t.getTime()<=now.getTime())t.setDate(t.getDate()+1);
  return t;
}
function botNeutralWeights(){const w={};BOT_SIGNALS.forEach(s=>w[s.id]=1);return w;}
function botDefaultState(){
  const learn={}; BOT_SIGNALS.forEach(s=>learn[s.id]={hits:0,total:0});
  const setups={}; BOT_SETUPS.forEach(x=>setups[x[0]]={hits:0,total:0,sumRet:0,mult:1});
  const weightsR={}; BOT_REGIMES.forEach(r=>weightsR[r]=botNeutralWeights());
  return {version:3,equity:BOT_START_EQUITY,startEquity:BOT_START_EQUITY,
    netDeposits:0,cashFlows:[],activity:[],createdAt:Date.now(),
    weightsR,learn,setups,params:Object.assign({},BOT_DEFAULT_PARAMS),
    trades:[],positions:[],pending:[],lastPx:{},news:null,study:null,
    lastRunDay:null,lastScan:null,pretrained:false,pretrain:null,
    startPrice:null,startDate:null,lessons:[],seq:1};
}
/* upgrade older saved states in place: v1 (single open) -> v2 (portfolio) -> v3 (regimes) */
function botMigrate(st){
  if(!st)return st;
  if(st.version<2||st.open!==undefined){
    st.version=2;
    st.positions=st.positions||[];
    if(st.open){const o=st.open;o.sym=o.sym||'BTC';o.setup=o.setup||'morning';o.id=1;st.positions.push(o);delete st.open;}
    st.pending=st.pending||[]; st.lastPx=st.lastPx||{}; st.seq=st.seq||100;
    if(!st.setups){const setups={};BOT_SETUPS.forEach(x=>setups[x[0]]={hits:0,total:0,sumRet:0,mult:1});st.setups=setups;}
    if(st.lastDecision&&!st.lastScan)st.lastScan={date:st.lastDecision.date,ranAt:st.lastDecision.ranAt,late:!!st.lastDecision.late,byAsset:{BTC:st.lastDecision}};
    st.trades=(st.trades||[]).map(t=>Object.assign({sym:'BTC',setup:'morning'},t));
  }
  if(st.version<3){
    st.version=3;
    const flat=st.weights||botNeutralWeights();
    st.weightsR={};BOT_REGIMES.forEach(r=>{st.weightsR[r]={};BOT_SIGNALS.forEach(s=>st.weightsR[r][s.id]=flat[s.id]!=null?flat[s.id]:1);});
    delete st.weights;
    st.params=st.params||Object.assign({},BOT_DEFAULT_PARAMS);
    st.news=st.news||null; st.study=st.study||null;
    BOT_SIGNALS.forEach(s=>{if(!st.learn[s.id])st.learn[s.id]={hits:0,total:0};});
  }
  /* additive fields (safe for any version) */
  st.netDeposits=st.netDeposits||0;
  st.cashFlows=st.cashFlows||[];
  st.activity=st.activity||[];
  st.createdAt=st.createdAt||(st.pretrain&&st.pretrain.when)||Date.now();
  return st;
}
/* append-only operational ledger: every open/close/fill/expiry/scan is recorded */
function botLog(st,kind,txt){
  st.activity=st.activity||[];
  st.activity.push({ts:Date.now(),kind,txt});
  if(st.activity.length>200)st.activity=st.activity.slice(-200);
}
/* serialize all bot operations — two flows can never clobber each other's state */
let _botChain=Promise.resolve();
function botQueue(fn){
  const p=_botChain.then(fn,fn);
  _botChain=p.then(()=>{},()=>{});
  return p;
}
function botStorageGet(){
  return new Promise(res=>{
    try{
      if(typeof chrome!=='undefined'&&chrome.storage&&chrome.storage.local){
        chrome.storage.local.get('botState',o=>res((o&&o.botState)||null));return;
      }
    }catch(e){}
    try{res(JSON.parse(localStorage.getItem('botState')||'null'));}catch(e){res(null);}
  });
}
function botStorageSet(st){
  return new Promise(res=>{
    try{
      if(typeof chrome!=='undefined'&&chrome.storage&&chrome.storage.local){
        chrome.storage.local.set({botState:st},()=>res(true));return;
      }
    }catch(e){}
    try{localStorage.setItem('botState',JSON.stringify(st));}catch(e){}
    res(true);
  });
}
async function botLoad(){const st=await botStorageGet();return botMigrate(st)||botDefaultState();}
function botSave(st){return botStorageSet(st);}
function botNeedsRun(st,now){
  now=now||new Date();
  const after=now.getHours()>BOT_RUN_HOUR||(now.getHours()===BOT_RUN_HOUR&&now.getMinutes()>=BOT_RUN_MIN);
  return after&&st.lastRunDay!==botDayStr(now);
}

/* ====================== NEWS RADAR ======================
   Headlines from major crypto outlets (same stories that move X/Twitter),
   scored by a keyword lexicon: sentiment (bullish/bearish) and expected
   volatility impact (Fed, hacks, ETF decisions, lawsuits...). */
const BOT_FEEDS=[
  ['CoinDesk','https://www.coindesk.com/arc/outboundfeeds/rss'],
  ['Cointelegraph','https://cointelegraph.com/rss'],
  ['Decrypt','https://decrypt.co/feed']
];
const BOT_LEX={
  pos:[['etf approv',2.5],['etf inflow',2],['adoption',1],['halving',1],['rate cut',2],['institutional',1.2],['all-time high',1.5],['rally',1.2],['bullish',1],['accumulat',1],['buys',1],['reserve',1],['upgrade',0.8],['partnership',0.8],['surge',1.2]],
  neg:[['hack',2.5],['exploit',2],['stolen',2],['lawsuit',1.5],['sues',2],['ban',1.8],['crash',2],['liquidat',1.5],['selloff',1.5],['sell-off',1.5],['bearish',1],['fraud',2],['bankrupt',2.5],['recession',1.5],['plunge',1.5],['tariff',1.2],['scam',1.5],['outflow',1.2],['dump',1],['warning',0.8]],
  vol:[['fed ',1.5],['fomc',2],['cpi',1.8],['inflation',1.2],['etf',1],['hack',2],['war',2],['election',1.2],['sec ',1.2],['regulat',1],['halving',1],['liquidat',1.5],['crash',2],['emergency',2],['tariff',1.2]]
};
function botScoreHeadline(title){
  const s=' '+title.toLowerCase()+' ';let sent=0,vol=0;
  BOT_LEX.pos.forEach(x=>{if(s.indexOf(x[0])>=0)sent+=x[1];});
  BOT_LEX.neg.forEach(x=>{if(s.indexOf(x[0])>=0)sent-=x[1];});
  BOT_LEX.vol.forEach(x=>{if(s.indexOf(x[0])>=0)vol+=x[1];});
  return{sent,vol};
}
async function botFetchNews(){
  const items=[];
  for(const f of BOT_FEEDS){
    try{
      const r=await fetch(f[1]);if(!r.ok)continue;
      const xml=await r.text();
      const chunks=xml.split('<item>').slice(1,16);
      for(const ch of chunks){
        const mt=ch.match(/<title>(?:<!\[CDATA\[)?([\s\S]*?)(?:\]\]>)?<\/title>/);if(!mt)continue;
        const title=mt[1].replace(/<[^>]+>/g,'').replace(/&amp;/g,'&').replace(/&#39;|&apos;/g,"'").replace(/&quot;/g,'"').trim();
        if(!title)continue;
        const md=ch.match(/<pubDate>([^<]+)<\/pubDate>/);
        const ts=md?Date.parse(md[1]):Date.now();
        if(isFinite(ts)&&Date.now()-ts>36*3600000)continue; // only last 36h
        const sc=botScoreHeadline(title);
        items.push({t:title.slice(0,140),src:f[0],ts,sent:+sc.sent.toFixed(1),vol:+sc.vol.toFixed(1)});
      }
    }catch(e){}
  }
  if(!items.length)return null;
  const sent=Math.max(-1,Math.min(1,items.reduce((a,x)=>a+x.sent,0)/12));
  const vol=Math.max(0,Math.min(1,items.reduce((a,x)=>a+x.vol,0)/25));
  const top=items.filter(x=>Math.abs(x.sent)+x.vol>0)
    .sort((a,b)=>(Math.abs(b.sent)+b.vol)-(Math.abs(a.sent)+a.vol)).slice(0,5);
  return {at:Date.now(),sent:+sent.toFixed(2),vol:+vol.toFixed(2),n:items.length,top};
}
function botNewsFresh(news){return !!(news&&Date.now()-news.at<24*3600000);}
function botNewsVote(news){if(!botNewsFresh(news))return 0;return news.sent>=0.25?1:news.sent<=-0.25?-1:0;}

/* Per-bar feature votes + market regime. Powers live decisions, pretraining
   and the nightly strategy simulations. */
function botSeries(S,fngArr){
  const {h,l,c,v}=S,n=c.length;
  const sig=signalNormSeries(S);
  const E20=ema(c,20),E50=ema(c,50),E200=sig.e200,MM=macdArr(c),HIST=MM.h;
  const R2=rsiArr(c,2),BB=boll(c),AT=atrArr(h,l,c);
  const atrPctArr=AT.map((a,i)=>a!=null?a/c[i]*100:null);
  const volBase=ema(atrPctArr.map(x=>x==null?0:x),100);
  const wk=resampleSeries(S,7),wkE=ema(wk.c,30);
  const wkTrend=wk.c.map((cc,i)=>wkE[i]!=null?Math.sign(cc-wkE[i]):0);
  const weeklyAt=ts=>{let r=0;for(let i=0;i<wk.t.length;i++){if(wk.t[i]<=ts)r=wkTrend[i];else break;}return r;};
  let fngByDay=null;
  if(fngArr&&fngArr.length){fngByDay={};fngArr.forEach(d=>{fngByDay[botDayStr(new Date(d.t))]=d.v;});}
  const votesAt=i=>{
    if(i<210)return null;
    if(sig.stDir[i]==null||E200[i]==null||sig.norm[i]==null||HIST[i]==null||AT[i]==null)return null;
    const price=c[i],votes={};
    votes.st=sig.stDir[i]>0?1:-1;
    votes.e200=price>E200[i]?1:-1;
    votes.comp=sig.norm[i]>0.15?1:(sig.norm[i]<-0.15?-1:0);
    votes.cross=(E50[i]!=null)?(E50[i]>E200[i]?1:-1):0;
    votes.macd=HIST[i]>0?1:-1;
    let hh=-1e18,ll=1e18;for(let j=Math.max(0,i-20);j<i;j++){hh=Math.max(hh,h[j]);ll=Math.min(ll,l[j]);}
    votes.brk=price>hh?1:(price<ll?-1:0);
    votes.rsi2=R2[i]==null?0:(R2[i]<10?1:(R2[i]>90?-1:0));
    const pb=(BB.up[i]==null||BB.up[i]===BB.lo[i])?0.5:(price-BB.lo[i])/(BB.up[i]-BB.lo[i]);
    votes.bbx=pb<0.05?1:(pb>0.95?-1:0);
    votes.wk=weeklyAt(S.t[i]);
    let fv=0;
    if(fngByDay){const x=fngByDay[botDayStr(new Date(S.t[i]))];if(x!=null){if(x<=25)fv=1;else if(x>=75)fv=-1;}}
    votes.fng=fv;
    votes.news=0; // historical bars have no news feed; live scans set it
    const bull=price>=E200[i];
    const volHi=(atrPctArr[i]!=null&&volBase[i]!=null&&volBase[i]>0)?atrPctArr[i]>1.25*volBase[i]:false;
    const regime=(bull?'bull':'bear')+(volHi?'Vol':'Calm');
    /* near-term trend (the recent tape): the bot must not fight a strong
       multi-day move just because the slow 200-day frame disagrees. +1 up,
       -1 down, 0 mixed. Two ways to qualify: price on one side of the 20-day
       EMA with the EMA sloping that way, OR a sharp 7-day move (>3× daily ATR)
       that the lagging average hasn't caught up to yet. */
    let nearTrend=0;
    if(E20[i]!=null&&E20[i-5]!=null){
      const ret7=i>=7?(price/c[i-7]-1)*100:0;
      const sharp=Math.abs(ret7)>3*Math.max(AT[i]/price*100,0.8);
      const up=price>E20[i]&&(E20[i]>E20[i-5]||(sharp&&ret7>0));
      const dn=price<E20[i]&&(E20[i]<E20[i-5]||(sharp&&ret7<0));
      if(up&&!dn)nearTrend=1; else if(dn&&!up)nearTrend=-1;
    }
    return {votes,atrPct:AT[i]/price*100,price,t:S.t[i],regime,nearTrend};
  };
  return {votesAt,n,atr:AT};
}
function botScore(votes,weights){
  let sw=0,wsAll=0;
  BOT_SIGNALS.forEach(s=>{const w=(weights&&weights[s.id])||1;wsAll+=w;sw+=w*(votes[s.id]||0);});
  return wsAll>0?sw/wsAll:0;
}
function botW(st,regime){return (st.weightsR&&st.weightsR[regime])||botNeutralWeights();}
function botSetupMult(st,id){const s=st&&st.setups&&st.setups[id];return s?s.mult:1;}
function botRiskOf(p){if(p.scaled||p.stop==null)return 0;return (p.sizePct/100)*(Math.abs(p.entry-p.stop)/p.entry*100);}
function botUsedRisk(st){return st.positions.reduce((a,p)=>a+botRiskOf(p),0);}
function botDecide(f,st,setupId){
  const p=st.params||BOT_DEFAULT_PARAMS;
  const W=botW(st,f.regime);
  const score=botScore(f.votes,W);
  const conf=Math.min(1,Math.abs(score)/0.4);
  let action='FLAT';
  if(score>=p.th)action='LONG';else if(score<=-p.th)action='SHORT';
  const lastN=(st&&st.trades?st.trades.slice(-3):[]);
  const brake=(lastN.length===3&&lastN.every(t=>t.ret<=0))?0.5:1;
  const newsBrake=(botNewsFresh(st.news)&&st.news.vol>=0.6)?0.7:1; // event risk: smaller size
  const sMult=botSetupMult(st,setupId||'morning');
  const stopDist=p.stopATR*Math.max(f.atrPct,0.5);
  const riskPct=(BOT_RISK_MIN+(BOT_RISK_MAX-BOT_RISK_MIN)*conf)*brake*newsBrake*sMult;
  let sizePct=sMult<=0?0:Math.round(Math.max(5,Math.min(100,riskPct/stopDist*100)));
  if(action==='FLAT')sizePct=0;
  const atrAbs=f.price*f.atrPct/100;
  const dir=action==='LONG'?1:-1;
  const stop=action==='FLAT'?null:f.price-dir*p.stopATR*atrAbs;
  const t1=action==='FLAT'?null:f.price+dir*p.stopATR*atrAbs;
  const t2=action==='FLAT'?null:f.price+dir*p.t2ATR*atrAbs;
  const reasons=BOT_SIGNALS
    .map(s=>({id:s.id,name:s.name,v:f.votes[s.id]||0,w:W[s.id]||1}))
    .filter(r=>r.v!==0)
    .sort((a,b)=>Math.abs(b.w*b.v)-Math.abs(a.w*a.v));
  return {action,score,conf,sizePct,stop,t1,t2,reasons,brake:brake<1,newsBrake:newsBrake<1,
    atrPct:f.atrPct,riskPct:+riskPct.toFixed(2),regime:f.regime,trailATR:p.trailATR};
}
/* learning: signals that voted are rewarded/punished by the move they
   predicted — in the weight set of the regime the trade was opened in,
   with recency decay on the displayed accuracy stats */
function botLearnFrom(st,votes,entry,exit,atrPctEntry,regime){
  const mkt=(exit-entry)/entry;
  const m=Math.min(2,Math.abs(mkt)*100/Math.max(atrPctEntry||2,0.5));
  const regs=regime&&st.weightsR[regime]?[regime]:BOT_REGIMES;
  const eta=regs.length>1?BOT_ETA/2:BOT_ETA;
  let bigId=null,bigDelta=0,bigW=1;
  BOT_SIGNALS.forEach(s=>{
    const v=votes&&votes[s.id]?votes[s.id]:0; if(!v)return;
    const correct=(v>0&&mkt>0)||(v<0&&mkt<0);
    regs.forEach(rg=>{
      const W=st.weightsR[rg];const w0=W[s.id]||1;
      let w=w0*(correct?(1+eta*m):(1-eta*m));
      w=Math.max(BOT_W_MIN,Math.min(BOT_W_MAX,w));
      W[s.id]=+w.toFixed(4);
      const d=Math.abs(w-w0);if(d>bigDelta){bigDelta=d;bigId=s.id;bigW=w;}
    });
    const L=st.learn[s.id]||(st.learn[s.id]={hits:0,total:0});
    L.hits=L.hits*BOT_DECAY+(correct?1:0);
    L.total=L.total*BOT_DECAY+1;
  });
  if(bigId){
    const sg=BOT_SIGNALS.find(x=>x.id===bigId);
    st.lessons.push({ts:Date.now(),txt:(sg?sg.name:bigId)+(bigW>1?' has been reliable — weight up to ':' keeps missing — weight cut to ')+bigW.toFixed(2)+(regime?' ('+(BOT_REGIME_NAMES[regime]||regime)+')':'')});
    st.lessons=st.lessons.slice(-12);
  }
}
const BOT_REASON_TXT={stop:'stop loss',trail:'trailing stop',target:'final target',time:'time limit','signal flip':'signal flip',manual:'closed by you'};
function botCloseTrade(st,pos,exit,exitT,reason){
  if(!pos)return null;
  const leg=p=>(pos.dir===1?(p-pos.entry)/pos.entry:(pos.entry-p)/pos.entry)*100;
  const ret=(pos.scaled?0.5*leg(pos.t1)+0.5*leg(exit):leg(exit))-BOT_COST;
  const eqBefore=st.equity;
  st.equity=+(st.equity*(1+(ret/100)*(pos.sizePct/100))).toFixed(2);
  const usd=+(st.equity-eqBefore).toFixed(2);
  botLog(st,ret>0?'win':'loss',(pos.sym||'BTC')+' '+(pos.dir===1?'LONG':'SHORT')+' closed: '+(usd>=0?'+$':'−$')+Math.abs(usd).toFixed(2)+' ('+(ret>=0?'+':'')+ret.toFixed(1)+'%) — '+(BOT_REASON_TXT[reason]||reason));
  const tr={sym:pos.sym||'BTC',setup:pos.setup||'morning',regime:pos.regime||null,dir:pos.dir,
    entry:pos.entry,exit:+exit.toFixed(2),entryT:pos.entryT,exitT,ret:+ret.toFixed(2),
    sizePct:pos.sizePct,reason,date:pos.date,votes:pos.votes,atrPct:pos.atrPct,scaled:!!pos.scaled,
    usd:usd,eqAfter:st.equity};
  st.trades.push(tr);st.trades=st.trades.slice(-400);
  const exitBlend=pos.scaled?0.5*(pos.t1+exit):exit;
  botLearnFrom(st,pos.votes,pos.entry,exitBlend,pos.atrPct,pos.regime);
  const ss=st.setups&&st.setups[tr.setup];
  if(ss){ss.total++;if(ret>0)ss.hits++;ss.sumRet+=ret;
    const old=ss.mult, avg=ss.sumRet/ss.total;
    ss.mult=(ss.total>=12&&avg<-0.3)?0:(ss.total>=8&&avg<0)?0.5:1;
    if(ss.mult<old){const nm=(BOT_SETUPS.find(x=>x[0]===tr.setup)||[0,tr.setup])[1];
      st.lessons.push({ts:Date.now(),txt:nm+(ss.mult===0?' disabled — losing on average over '+ss.total+' trades':' size halved — weak average result')});
      st.lessons=st.lessons.slice(-12);}}
  st.positions=st.positions.filter(p=>p.id!==pos.id);
  return tr;
}
/* Walk bars since entry (hourly when available). Stop first, then targets.
   At T1: bank 50%, stop -> breakeven, then trail behind the best price. */
function botEvaluateOpen(st,pos,S){
  const o=pos;if(!o)return;
  const atrAbs=o.entry*(o.atrPct||2)/100;
  const trailW=(o.trailATR||BOT_TRAIL_ATR)*atrAbs;
  if(o.t1==null)o.t1=o.entry+o.dir*1.6*atrAbs;
  if(o.t2==null)o.t2=(o.target!=null)?o.target:o.entry+o.dir*3.2*atrAbs;
  if(o.peak==null)o.peak=o.entry;
  if(o.scaled==null)o.scaled=false;
  const n=S.c.length;
  for(let i=0;i<n;i++){
    if(S.t[i]<=o.entryT)continue;
    const hi=S.h[i],lo=S.l[i];
    if(o.dir===1){
      if(o.stop!=null&&lo<=o.stop){botCloseTrade(st,o,o.stop,S.t[i],o.scaled?'trail':'stop');return;}
      if(!o.scaled){if(hi>=o.t1){o.scaled=true;o.stop=o.entry;}}
      else if(hi>=o.t2){botCloseTrade(st,o,o.t2,S.t[i],'target');return;}
      if(hi>o.peak)o.peak=hi;
      if(o.scaled){const tr=o.peak-trailW;if(o.stop==null||tr>o.stop)o.stop=tr;}
    }else{
      if(o.stop!=null&&hi>=o.stop){botCloseTrade(st,o,o.stop,S.t[i],o.scaled?'trail':'stop');return;}
      if(!o.scaled){if(lo<=o.t1){o.scaled=true;o.stop=o.entry;}}
      else if(lo<=o.t2){botCloseTrade(st,o,o.t2,S.t[i],'target');return;}
      if(lo<o.peak)o.peak=lo;
      if(o.scaled){const tr=o.peak+trailW;if(o.stop==null||tr<o.stop)o.stop=tr;}
    }
    if((S.t[i]-o.entryT)/86400000>=BOT_MAX_HOLD){botCloseTrade(st,o,S.c[i],S.t[i],'time');return;}
  }
}
/* Pending orders armed at the morning scan */
function botMakePendings(st,sym,f,S,score,now){
  if(Math.abs(score)<BOT_PEND_TH)return;
  const lean=score>0?1:-1;
  const p=st.params||BOT_DEFAULT_PARAMS;
  const atrAbs=f.price*f.atrPct/100;
  const conf=Math.min(1,Math.abs(score)/0.4);
  const newsBrake=(botNewsFresh(st.news)&&st.news.vol>=0.6)?0.7:1;
  const mk=(type,trigger)=>{
    if(trigger<=0)return;
    if(st.pending.some(x=>x.sym===sym&&x.type===type))return;
    const setupId=type==='dip'?'dip':'brk';
    const sMult=botSetupMult(st,setupId); if(sMult<=0)return;
    const stop=trigger-lean*p.stopATR*atrAbs, t1=trigger+lean*p.stopATR*atrAbs, t2=trigger+lean*p.t2ATR*atrAbs;
    const stopDist=p.stopATR*Math.max(f.atrPct,0.5);
    const riskPct=(BOT_RISK_MIN+(BOT_RISK_MAX-BOT_RISK_MIN)*conf)*sMult*newsBrake;
    const sizePct=Math.round(Math.max(5,Math.min(100,riskPct/stopDist*100)));
    st.pending.push({id:st.seq++,sym,type,dir:lean,trigger,stop,t1,t2,sizePct,votes:f.votes,atrPct:f.atrPct,
      regime:f.regime,trailATR:p.trailATR,created:Date.now(),expires:Date.now()+BOT_PEND_HOURS*3600000,
      reasons:['armed '+botDayStr(now||new Date())+' · lean '+(lean>0?'long':'short')]});
  };
  mk('dip',f.price-lean*BOT_DIP_ATR*atrAbs);
  const c=S.c,h=S.h,l=S.l,i=c.length-1;let hh=-1e18,ll=1e18;
  for(let j=Math.max(0,i-20);j<i;j++){hh=Math.max(hh,h[j]);ll=Math.min(ll,l[j]);}
  mk('brk',lean>0?hh+0.1*atrAbs:ll-0.1*atrAbs);
}
/* fill pending orders whose trigger was touched; drop expired ones */
function botCheckPendings(st,sym,H,now){
  now=now||new Date();
  st.pending=st.pending.filter(p=>{
    if(p.sym===sym&&now.getTime()>p.expires){botLog(st,'info',sym+' pending '+(p.type==='dip'?'dip-buy':'breakout')+' expired untouched');return false;}
    return true;});
  for(const p of st.pending.filter(x=>x.sym===sym).slice()){
    let fillT=null;
    for(let i=0;i<H.c.length;i++){
      if(H.t[i]<=p.created)continue;
      const hit=p.dir===1?(p.type==='dip'?H.l[i]<=p.trigger:H.h[i]>=p.trigger)
                         :(p.type==='dip'?H.h[i]>=p.trigger:H.l[i]<=p.trigger);
      if(hit){fillT=H.t[i];break;}
    }
    if(!fillT)continue;
    st.pending=st.pending.filter(x=>x.id!==p.id);
    const risk=(p.sizePct/100)*(Math.abs(p.trigger-p.stop)/p.trigger*100);
    if(botUsedRisk(st)+risk>BOT_RISK_BUDGET+0.01)continue;
    if(botSetupMult(st,p.type==='dip'?'dip':'brk')<=0)continue;
    const refP=last(H.c); // no pyramiding: skip if it would add to a same-direction loser
    if(st.positions.some(q=>q.sym===sym&&q.dir===p.dir&&((q.dir===1&&refP<q.entry)||(q.dir===-1&&refP>q.entry)))){
      botLog(st,'info',sym+' pending '+(p.type==='dip'?'dip-buy':'breakout')+' cancelled — would add to a losing position');continue;}
    st.positions.push({id:st.seq++,sym,dir:p.dir,entry:p.trigger,entryT:fillT,stop:p.stop,t1:p.t1,t2:p.t2,
      peak:p.trigger,scaled:false,sizePct:p.sizePct,votes:p.votes,atrPct:p.atrPct,regime:p.regime,trailATR:p.trailATR,
      date:botDayStr(new Date(fillT)),setup:p.type==='dip'?'dip':'brk',reasons:p.reasons});
    botLog(st,'open',sym+' '+(p.dir===1?'LONG':'SHORT')+' opened at $'+Math.round(p.trigger).toLocaleString('en-US')+' · '+p.sizePct+'% ('+(p.type==='dip'?'dip-buy filled':'breakout filled')+')');
  }
}
/* Morning routine: per asset — exits, pendings, decision, entry, fresh pendings */
async function _botRunMorning(opts){
  opts=opts||{};
  const now=opts.now||new Date();
  const st=await botLoad();
  const today=botDayStr(now);
  if(!opts.force&&st.lastRunDay===today)return{skipped:true,state:st};
  const fng=await fetchSentiment(10).catch(()=>null);
  try{const nw=await botFetchNews();if(nw)st.news=nw;}catch(e){}
  const byAsset={};
  for(const sym of BOT_ASSETS){
    let S; try{S=await loadDailyFor(sym,900);}catch(e){continue;}
    let H=null; try{H=await fetchBinancePaged(sym,'1h',400);}catch(e){}
    st.lastPx[sym]=last((H||S).c);
    if(sym==='BTC'&&!st.startPrice){st.startPrice=last(S.c);st.startDate=today;}
    for(const pos of st.positions.filter(p=>p.sym===sym).slice())botEvaluateOpen(st,pos,H||S);
    if(H)botCheckPendings(st,sym,H,now);
    const ser=botSeries(S,fng);
    const f=ser.votesAt(S.c.length-1);
    if(!f)continue;
    f.votes.news=botNewsVote(st.news);
    const d=botDecide(f,st,'morning');
    for(const pos of st.positions.filter(p=>p.sym===sym).slice()){
      const opp=(pos.dir===1&&d.action==='SHORT')||(pos.dir===-1&&d.action==='LONG');
      if(opp&&pos.setup!=='manual')botCloseTrade(st,pos,f.price,f.t,'signal flip'); // your manual trades live by their own stop/target, not the bot's opinion
    }
    const hasMorning=st.positions.some(p=>p.sym===sym&&p.setup==='morning');
    const dir=d.action==='LONG'?1:-1;
    const fightsTrend=d.action!=='FLAT'&&f.nearTrend!==0&&f.nearTrend!==dir; // entry opposes the recent tape
    const sameDirUnderwater=st.positions.some(p=>p.sym===sym&&p.dir===dir&&
      ((p.dir===1&&f.price<p.entry)||(p.dir===-1&&f.price>p.entry))); // would pyramid into a loser
    if(!hasMorning&&d.action!=='FLAT'&&d.sizePct>0){
      const risk=(d.sizePct/100)*(Math.abs(f.price-d.stop)/f.price*100);
      if(fightsTrend){
        botLog(st,'info',sym+' '+d.action+' skipped — fights the '+(f.nearTrend>0?'up':'down')+'trend of the last 2 weeks');
      }else if(sameDirUnderwater){
        botLog(st,'info',sym+' '+d.action+' skipped — would add to a losing '+d.action+' (no pyramiding)');
      }else if(botUsedRisk(st)+risk<=BOT_RISK_BUDGET+0.01){
        st.positions.push({id:st.seq++,sym,dir,entry:f.price,entryT:f.t,
          stop:d.stop,t1:d.t1,t2:d.t2,peak:f.price,scaled:false,sizePct:d.sizePct,
          votes:f.votes,atrPct:f.atrPct,regime:f.regime,trailATR:d.trailATR,date:today,setup:'morning',
          reasons:d.reasons.slice(0,4).map(r=>r.name+(r.v>0?' ▲':' ▼'))});
        botLog(st,'open',sym+' '+d.action+' opened at $'+Math.round(f.price).toLocaleString('en-US')+' · '+d.sizePct+'% (morning signal)');
      }else{
        botLog(st,'info',sym+' '+d.action+' skipped — risk budget full');
      }
    }
    if(!fightsTrend)botMakePendings(st,sym,f,S,d.score,now); // don't arm orders against the recent tape
    byAsset[sym]={action:d.action,score:+d.score.toFixed(3),conf:+d.conf.toFixed(2),sizePct:d.sizePct,
      riskPct:d.riskPct,price:f.price,brake:d.brake,newsBrake:d.newsBrake,regime:f.regime,atrPct:+f.atrPct.toFixed(2),
      reasons:d.reasons.slice(0,5).map(r=>({name:r.name,v:r.v,w:+r.w.toFixed(2)}))};
  }
  if(Object.keys(byAsset).length>0)st.lastRunDay=today; // don't mark done if all assets failed (allows retry on next alarm)
  st.lastScan={date:today,ranAt:Date.now(),late:now.getHours()>=9,byAsset};
  botLog(st,'info','Scan '+today+': '+BOT_ASSETS.map(s=>byAsset[s]?s+' '+byAsset[s].action:s+' n/a').join(' · '));
  await botSave(st);
  return{state:st,scan:st.lastScan};
}
/* Hourly watcher: exits + pending fills + price refresh + stale-news refresh */
async function _botCheckExits(){
  const st=await botLoad();
  const syms=Array.from(new Set(st.positions.map(p=>p.sym).concat(st.pending.map(p=>p.sym))));
  if(!st.news||Date.now()-st.news.at>3*3600000){try{const nw=await botFetchNews();if(nw)st.news=nw;}catch(e){}}
  if(!syms.length){await botSave(st);return{state:st,checked:false};}
  const before=JSON.stringify([st.trades.length,st.positions,st.pending.length]);
  for(const sym of syms){
    let H=null;
    try{H=await fetchBinancePaged(sym,'1h',400);}catch(e){}
    if(!H){try{H=await loadDailyFor(sym,30);}catch(e){continue;}}
    st.lastPx[sym]=last(H.c);
    for(const pos of st.positions.filter(p=>p.sym===sym).slice())botEvaluateOpen(st,pos,H);
    botCheckPendings(st,sym,H,new Date());
  }
  const after=JSON.stringify([st.trades.length,st.positions,st.pending.length]);
  await botSave(st);
  return{state:st,checked:true,closed:before!==after};
}

/* ====================== NIGHTLY STUDY ======================
   Re-learns regime weights on fresh data (blended 50/50 with what live
   trading taught), then walk-forward-tests 81 strategy variants: tuned on
   the older 70% of the window, validated on the newest 30%, adopted only
   if clearly better out-of-sample. */
function botFreshWeights(ser,S){
  const wR={};BOT_REGIMES.forEach(r=>wR[r]=botNeutralWeights());
  for(let i=210;i<S.c.length-1;i++){
    const f=ser.votesAt(i);if(!f)continue;
    const mkt=(S.c[i+1]-S.c[i])/S.c[i];
    const m=Math.min(2,Math.abs(mkt)*100/Math.max(f.atrPct,0.5));
    const W=wR[f.regime];
    BOT_SIGNALS.forEach(s=>{const v=f.votes[s.id]||0;if(!v)return;
      const ok=(v>0&&mkt>0)||(v<0&&mkt<0);
      W[s.id]=Math.max(BOT_W_MIN,Math.min(BOT_W_MAX,W[s.id]*(ok?(1+BOT_ETA*m):(1-BOT_ETA*m))));});
  }
  BOT_REGIMES.forEach(r=>BOT_SIGNALS.forEach(s=>wR[r][s.id]=+wR[r][s.id].toFixed(4)));
  return wR;
}
function botSimParams(S,ser,weightsR,params,i0,i1){
  const c=S.c,h=S.h,l=S.l;
  let eq=1,peak=1,maxDD=0,trades=0,wins=0,pos=null;
  for(let i=i0;i<i1;i++){
    if(pos){
      const hi=h[i],lo=l[i];let exit=0,exitP=0;
      if(pos.dir===1){
        if(lo<=pos.stop){exit=1;exitP=pos.stop;}
        else{if(!pos.scaled&&hi>=pos.t1){pos.scaled=true;pos.stop=pos.entry;}
          else if(pos.scaled&&hi>=pos.t2){exit=1;exitP=pos.t2;}
          if(!exit){if(hi>pos.peak)pos.peak=hi;if(pos.scaled){const tr=pos.peak-params.trailATR*pos.atrA;if(tr>pos.stop)pos.stop=tr;}}}
      }else{
        if(hi>=pos.stop){exit=1;exitP=pos.stop;}
        else{if(!pos.scaled&&lo<=pos.t1){pos.scaled=true;pos.stop=pos.entry;}
          else if(pos.scaled&&lo<=pos.t2){exit=1;exitP=pos.t2;}
          if(!exit){if(lo<pos.peak)pos.peak=lo;if(pos.scaled){const tr=pos.peak+params.trailATR*pos.atrA;if(tr<pos.stop)pos.stop=tr;}}}
      }
      if(!exit&&i-pos.i>=BOT_MAX_HOLD){exit=1;exitP=c[i];}
      if(exit){
        const leg=p=>(pos.dir===1?(p-pos.entry)/pos.entry:(pos.entry-p)/pos.entry)*100;
        const ret=(pos.scaled?0.5*leg(pos.t1)+0.5*leg(exitP):leg(exitP))-BOT_COST;
        eq*=(1+(ret/100)*pos.size);trades++;if(ret>0)wins++;pos=null;
      }
    }
    if(!pos){
      const f=ser.votesAt(i);
      if(f){
        const sc=botScore(f.votes,weightsR[f.regime]);
        if(Math.abs(sc)>=params.th){
          const dir=sc>0?1:-1,atrA=f.price*f.atrPct/100;
          const stopDist=params.stopATR*Math.max(f.atrPct,0.5);
          const size=Math.min(1,1.5/stopDist);
          pos={dir,entry:f.price,i,stop:f.price-dir*params.stopATR*atrA,t1:f.price+dir*params.stopATR*atrA,
            t2:f.price+dir*params.t2ATR*atrA,peak:f.price,scaled:false,size,atrA};
        }
      }
    }
    let u=0;if(pos)u=(pos.dir===1?(c[i]-pos.entry)/pos.entry:(pos.entry-c[i])/pos.entry)*pos.size;
    const ce=eq*(1+u);if(ce>peak)peak=ce;const dd=(ce-peak)/peak*100;if(dd<maxDD)maxDD=dd;
  }
  if(pos){const leg=p=>(pos.dir===1?(p-pos.entry)/pos.entry:(pos.entry-p)/pos.entry)*100;
    const ret=(pos.scaled?0.5*leg(pos.t1)+0.5*leg(c[i1-1]):leg(c[i1-1]))-BOT_COST;
    eq*=(1+(ret/100)*pos.size);trades++;if(ret>0)wins++;}
  const ret=(eq-1)*100;
  return{ret:+ret.toFixed(1),maxDD:+maxDD.toFixed(1),trades,wins,score:+(ret/(1+Math.abs(maxDD))).toFixed(3)};
}
function botStudyParams(S,ser,weightsR,current){
  const n=S.c.length, i0=Math.max(220,n-700), split=Math.floor(i0+(n-i0)*0.7);
  const ths=[0.10,0.12,0.15],stops=[1.3,1.6,2.0],t2s=[2.6,3.2,4.0],trails=[1.6,2.0,2.5];
  const combos=[];ths.forEach(th=>stops.forEach(s=>t2s.forEach(t2=>trails.forEach(tr=>combos.push({th,stopATR:s,t2ATR:t2,trailATR:tr})))));
  const ranked=combos.map(p=>({p,train:botSimParams(S,ser,weightsR,p,i0,split)}))
    .filter(x=>x.train.trades>=4).sort((a,b)=>b.train.score-a.train.score).slice(0,6);
  const valCur=botSimParams(S,ser,weightsR,current,split,n);
  let best=null;
  ranked.forEach(x=>{const val=botSimParams(S,ser,weightsR,x.p,split,n);
    if(val.trades>=3&&(!best||val.score>best.val.score))best={p:x.p,val};});
  const adopted=!!(best&&best.val.score>valCur.score*1.1&&best.val.score>0);
  return{tested:combos.length,adopted,params:adopted?best.p:current,valBest:best?best.val:null,valCur};
}
async function _botNightly(){
  const st=await botLoad();
  try{
    const S=await loadDailyFor('BTC',2200);
    const fng=await fetchSentiment(2000).catch(()=>null); // use full F&G history so the fng signal trains properly
    const ser=botSeries(S,fng);
    const fresh=botFreshWeights(ser,S);
    BOT_REGIMES.forEach(r=>BOT_SIGNALS.forEach(s=>{
      const a=(st.weightsR[r]&&st.weightsR[r][s.id])||1, b=(fresh[r]&&fresh[r][s.id])||1;
      if(!st.weightsR[r])st.weightsR[r]={};
      st.weightsR[r][s.id]=+(0.5*a+0.5*b).toFixed(4);
    }));
    const study=botStudyParams(S,ser,st.weightsR,st.params||BOT_DEFAULT_PARAMS);
    st.params=study.params;
    st.study={at:Date.now(),tested:study.tested,adopted:study.adopted,
      best:study.valBest?{ret:study.valBest.ret,maxDD:study.valBest.maxDD}:null,
      cur:{ret:study.valCur.ret,maxDD:study.valCur.maxDD},params:st.params};
    if(study.adopted){
      st.lessons.push({ts:Date.now(),txt:'Nightly study: adopted new tuning (entry '+st.params.th+', stop '+st.params.stopATR+'×ATR, target '+st.params.t2ATR+'×ATR, trail '+st.params.trailATR+'×ATR) — better risk-adjusted out-of-sample'});
      st.lessons=st.lessons.slice(-12);
    }
    botLog(st,'info','Nightly: tested '+study.tested+' variants — '+(study.adopted?'adopted new tuning (th='+st.params.th+' stop='+st.params.stopATR+'×ATR)':'kept current tuning (th='+st.params.th+' stop='+st.params.stopATR+'×ATR)'));
    try{const nw=await botFetchNews();if(nw)st.news=nw;}catch(e){}
    await botSave(st);
  }catch(e){}
  return st;
}
/* Pre-training: regime weights from history + a first strategy study. */
async function _botPretrain(){
  const st=await botLoad();
  const S=await loadDailyFor('BTC',2200);
  const fng=await fetchSentiment(2000).catch(()=>null); // use full F&G history so the fng signal trains properly
  const ser=botSeries(S,fng);
  st.weightsR=botFreshWeights(ser,S);
  let act=0,hit=0;
  for(let i=210;i<S.c.length-1;i++){
    const f=ser.votesAt(i);if(!f)continue;
    const sc=botScore(f.votes,st.weightsR[f.regime]);
    const mkt=(S.c[i+1]-S.c[i])/S.c[i];
    if(Math.abs(sc)>=(st.params||BOT_DEFAULT_PARAMS).th){act++;if((sc>0&&mkt>0)||(sc<0&&mkt<0))hit++;}
  }
  try{
    const study=botStudyParams(S,ser,st.weightsR,st.params||BOT_DEFAULT_PARAMS);
    st.params=study.params;
    st.study={at:Date.now(),tested:study.tested,adopted:study.adopted,
      best:study.valBest?{ret:study.valBest.ret,maxDD:study.valBest.maxDD}:null,
      cur:{ret:study.valCur.ret,maxDD:study.valCur.maxDD},params:st.params};
  }catch(e){}
  st.lessons=[];
  st.pretrained=true;
  st.pretrain={days:S.c.length,signals:act,hitRate:act?+(hit/act*100).toFixed(1):0,when:Date.now()};
  await botSave(st);
  return st;
}
async function botEnsureReady(){
  let st=await botLoad();
  if(!st.pretrained){try{st=await botPretrain();}catch(e){await botSave(st);}}
  return st;
}
/* The bot's directional read for a symbol RIGHT NOW — used for the manual
   buy/sell "second opinion" warning. UI-free. */
function botView(dailyS,st,news){
  if(!dailyS||!dailyS.c||dailyS.c.length<211)return null;
  const ser=botSeries(dailyS,null);
  const f=ser.votesAt(dailyS.c.length-1);
  if(!f)return null;
  f.votes.news=botNewsVote(news||(st&&st.news));
  const d=botDecide(f,st,'manual');
  return {action:d.action,score:+d.score.toFixed(3),conf:+d.conf.toFixed(2),
    nearTrend:f.nearTrend,regime:f.regime,price:f.price,atrPct:f.atrPct,f,d};
}
/* Open a MANUAL paper trade (you, not the bot). Same risk-managed structure:
   stop & first target 1.6×ATR, final target, breakeven+trail; risk ~1.5% of
   equity; managed by the same hourly exit watcher. */
function botOpenManual(st,sym,dir,price,view){
  const p=st.params||BOT_DEFAULT_PARAMS;
  const atrPct=view&&view.atrPct?view.atrPct:2;
  const atrAbs=price*atrPct/100;
  const stopDist=p.stopATR*Math.max(atrPct,0.5);
  const sizePct=Math.round(Math.max(5,Math.min(100,1.5/stopDist*100)));
  const stop=price-dir*p.stopATR*atrAbs, t1=price+dir*p.stopATR*atrAbs, t2=price+dir*p.t2ATR*atrAbs;
  st.positions.push({id:st.seq++,sym,dir,entry:price,entryT:Date.now(),stop,t1,t2,peak:price,scaled:false,
    sizePct,votes:(view&&view.f?view.f.votes:{}),atrPct,regime:(view?view.regime:null),trailATR:p.trailATR,
    date:botDayStr(new Date()),setup:'manual',reasons:['manual '+(dir===1?'buy':'sell')+' — you']});
  botLog(st,'open',sym+' '+(dir===1?'LONG':'SHORT')+' opened at $'+Math.round(price).toLocaleString('en-US')+' · '+sizePct+'% (MANUAL — you)');
  return sizePct;
}

/* ===================== MINER BREAK-EVEN ESTIMATE =====================
   Rough "production cost" floor from live network hashrate (mempool.space,
   CORS-open, no key). Electricity-only break-even per BTC at a few power
   prices. It's an ESTIMATE — sensitive to miner efficiency and $/kWh. */
const MINER_EFF_JTH=25;        // network-avg miner efficiency, Joules per TH
const MINER_SUBSIDY=3.125;     // BTC per block after the 2024 halving
async function fetchMinerCost(){
  try{
    const r=await fetch("https://mempool.space/api/v1/mining/hashrate/3d");
    if(!r.ok)return null;
    const j=await r.json();
    const hps=j.currentHashrate; if(!hps||!isFinite(hps))return null;
    const ths=hps/1e12;                          // hashes/s -> TH/s
    const powerW=ths*MINER_EFF_JTH;              // J/s = W
    const kWhDay=powerW*24/1000;
    const btcDay=144*MINER_SUBSIDY;
    const perBTC=el=>Math.round(kWhDay*el/btcDay);
    return {at:Date.now(),hashrateEH:+(hps/1e18).toFixed(0),
      low:perBTC(0.04),mid:perBTC(0.05),high:perBTC(0.06),
      eff:MINER_EFF_JTH,subsidy:MINER_SUBSIDY};
  }catch(e){return null;}
}

function botSetBadge(st){
  try{
    if(typeof chrome==='undefined'||!chrome.action||!chrome.action.setBadgeText)return;
    const d=(st&&st.lastScan&&st.lastScan.byAsset&&st.lastScan.byAsset.BTC)||null;
    const n=st&&st.positions?st.positions.length:0;
    const txt=!d&&!n?'':(n>0?String(n):(d&&d.action==='LONG'?'▲':d&&d.action==='SHORT'?'▼':'—'));
    chrome.action.setBadgeText({text:txt});
    chrome.action.setBadgeBackgroundColor({color:d&&d.action==='LONG'?'#00c853':d&&d.action==='SHORT'?'#ff1744':'#5a5f5a'});
  }catch(e){}
}

/* public entry points run through the queue so operations never overlap */
function botRunMorning(opts){return botQueue(()=>_botRunMorning(opts));}
function botCheckExits(){return botQueue(()=>_botCheckExits());}
function botNightly(){return botQueue(()=>_botNightly());}
function botPretrain(){return botQueue(()=>_botPretrain());}
