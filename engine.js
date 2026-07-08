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


/* ============================================================================
   VISOR PUBLICO — sin estrategia. El cerebro (senales, pesos, decision,
   aprendizaje) vive en un repositorio privado y solo publica un resumen.
   ============================================================================ */
const BOT_ASSETS=['BTC','ETH'];
const BOT_REGIME_NAMES={bullCalm:'BULL · calm',bullVol:'BULL · volatile',bearCalm:'BEAR · calm',bearVol:'BEAR · volatile'};
const BOT_START_EQUITY=10000;
const BOT_RUN_HOUR=8, BOT_RUN_MIN=30;
const BOT_RISK_BUDGET=6.0;
const BOT_SETUPS=[['morning','Morning signal'],['dip','Dip-buy limit'],['brk','Breakout stop'],['manual','Manual'],['trend','Trend core']];
const BOT_SIGNALS=[];
function botPad(n){return (n<10?'0':'')+n;}
function botDayStr(d){return d.getFullYear()+'-'+botPad(d.getMonth()+1)+'-'+botPad(d.getDate());}
function botNextRun(now){const t=new Date(now.getFullYear(),now.getMonth(),now.getDate(),8,35,0,0);if(t.getTime()<=now.getTime())t.setDate(t.getDate()+1);return t;}
function botDefaultState(){return {version:3,equity:BOT_START_EQUITY,startEquity:BOT_START_EQUITY,netDeposits:0,cashFlows:[],
  activity:[],createdAt:Date.now(),cores:{},manualPnl:0,trades:[],positions:[],pending:[],lastPx:{},news:null,study:null,
  lastRunDay:null,lastScan:null,pretrained:true,pretrain:null,startPrice:null,startDate:null,lessons:[],setups:{},seq:1};}
function botMigrate(st){
  if(!st)return st;
  st.version=st.version||3;
  ['trades','positions','pending','activity','cashFlows','lessons'].forEach(k=>{st[k]=st[k]||[];});
  st.cores=st.cores||{};st.lastPx=st.lastPx||{};st.setups=st.setups||{};
  st.netDeposits=st.netDeposits||0;st.manualPnl=st.manualPnl||0;
  st.createdAt=st.createdAt||Date.now();
  return st;
}
function botLog(st,kind,txt){st.activity=st.activity||[];st.activity.push({ts:Date.now(),kind,txt});
  if(st.activity.length>200)st.activity=st.activity.slice(-200);}
let _botChain=Promise.resolve();
function botQueue(fn){const p=_botChain.then(fn,fn);_botChain=p.then(()=>{},()=>{});return p;}
function botStorageGet(){return new Promise(res=>{try{res(JSON.parse(localStorage.getItem('botState')||'null'));}catch(e){res(null);}});}
function botStorageSet(st){return new Promise(res=>{try{localStorage.setItem('botState',JSON.stringify(st));}catch(e){}res(true);});}
async function botLoad(){const st=await botStorageGet();return botMigrate(st)||botDefaultState();}
function botSave(st){return botStorageSet(st);}
function botNeedsRun(){return false;}   // el visor jamas opera localmente
function botUsedRisk(st){return (st.positions||[]).reduce((a,p)=>a+((p.scaled||p.stop==null)?0:(p.sizePct/100)*(Math.abs(p.entry-p.stop)/p.entry*100)),0);}
function botSetBadge(){ /* sin insignia en el visor */ }
const BOT_CLOUD_URL='https://jlsv305-droid.github.io/btc-pro/cloud-summary.json';
function botCloudFresh(st){return !!(st&&st.source==='cloud'&&st.cloudRunAt&&Date.now()-st.cloudRunAt<26*3600000);}
/* Devices sync from the PUBLIC SUMMARY (no weights/params/votes — the brain
   stays private in the cloud repo). Cloud fields overlay the local state;
   local-only knowledge (weights, params, manual layer) is preserved. */
async function botSyncCloud(){
  try{
    const r=await fetch(BOT_CLOUD_URL,{cache:'no-store'});if(!r.ok)return null;
    const sum=await r.json();
    if(!sum||!sum.cloudRunAt)return null;
    const local=await botLoad();
    if(local.source==='cloud'&&local.cloudRunAt&&local.cloudRunAt>=sum.cloudRunAt)return local;
    const manPos=(local.positions||[]).filter(p=>p.setup==='manual');
    const manTr=(local.trades||[]).filter(t=>t.localManual);
    const merged=botMigrate(Object.assign({},local,sum));
    merged.positions=(sum.positions||[]).filter(p=>p.setup!=='manual').concat(manPos);
    merged.trades=(sum.trades||[]).concat(manTr).slice(-400);
    merged.manualPnl=local.manualPnl||0;
    merged.lastPx=Object.assign({},local.lastPx||{},sum.lastPx||{});
    merged.source='cloud';
    await botSave(merged);
    return merged;
  }catch(e){return null;}
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

/* stubs: en el visor no hay cerebro local */
async function botEnsureReady(){const s=await botSyncCloud();return s||await botLoad();}
async function botPretrain(){return await botLoad();}
async function botRunMorning(){return {skipped:true,state:await botLoad()};}
async function botCheckExits(){const s=await botSyncCloud();return {state:s||await botLoad(),checked:!!s};}
async function botNightly(){return await botLoad();}
function botView(){return null;}
function botOpenManual(){return null;}
function botCloseTrade(){return null;}
function botCoreClose(){return null;}
function botScore(){return 0;}
