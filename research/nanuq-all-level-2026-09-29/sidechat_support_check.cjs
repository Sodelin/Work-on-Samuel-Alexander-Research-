// Received verbatim in the authorized support handoff from ephemeral chat
// 01a0ef7c-7cdc-7f00-a827-8a43b8ae0ffa on 2026-09-29.
// Only XML entity decoding and this provenance header were added on receipt.
function verifySupport(report) {
  const results=[];
  function choose(n,k){const out=[];function rec(i,a){if(a.length===k){out.push(a);return;}for(;i<n;i++)rec(i+1,[...a,i]);}rec(0,[]);return out;}
  for(let n=3;n<=6;n++){
    const full=(1<<n)-1,pairs=choose(n,2),quartets=choose(n,4),splits=[],index=new Map();
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let mask=0;for(let k=i+1;k<=j;k++)mask|=1<<k;let canonical=Math.min(mask,full^mask);index.set(canonical,splits.length);splits.push({i,j,mask:canonical});}
    const quartetContrib=splits.map(({mask})=>{let bits=0n;for(let qi=0;qi<quartets.length;qi++){const Q=quartets[qi];for(let t=0;t<3;t++){const left=(1<<Q[0])|(1<<Q[t+1]),right=Q.reduce((b,x)=>b|(1<<x),0)^left;if(((mask&left)===left&&(mask&right)===0)||((mask&right)===right&&(mask&left)===0))bits|=1n<<BigInt(3*qi+t);}}return bits;});
    let treeCases=0,selectedTrees=0,negative=0,mismatches=0,checks=0,boundaryFailures=0;const systems=new Map(),supportsSeen=new Set();
    for(let duplicate=0;duplicate<(1<<n);duplicate++){
      const positions=Array.from({length:n},()=>[]),tips=[];
      for(let x=0;x<n;x++){positions[x].push(tips.length);tips.push(x);if((duplicate>>x)&1){positions[x].push(tips.length);tips.push(x);}}
      const m=tips.length,choices=[];
      function chooseOccurrences(x,selected){if(x===n){choices.push(selected);return;}for(const p of positions[x])chooseOccurrences(x+1,[...selected,p]);}
      chooseOccurrences(0,[]);
      const choiceEdgeSplitBits=choices.map(selected=>{const table=Array(m*m).fill(0);for(let lo=1;lo<m;lo++)for(let hi=lo;hi<m;hi++){let mask=0;for(let x=0;x<n;x++)if(selected[x]>=lo&&selected[x]<=hi)mask|=1<<x;if(mask&&mask!==full){const si=index.get(Math.min(mask,full^mask));if(si===undefined)throw Error("Noncircular selected edge");table[lo*m+hi]=1<<si;}}return table;});
      const memo=new Map();
      function orderedTrees(lo,hi){const key=lo*m+hi;if(memo.has(key))return memo.get(key);let out=[];if(lo===hi)out=[[key]];else for(let mid=lo;mid<hi;mid++)for(const a of orderedTrees(lo,mid))for(const b of orderedTrees(mid+1,hi))out.push([key,...a,...b]);memo.set(key,out);return out;}
      for(const edges of orderedTrees(1,m-1)){
        treeCases++;let allSupport=0;
        for(const table of choiceEdgeSplitBits){selectedTrees++;let support=0;for(const e of edges)support|=table[e];allSupport|=support;}
        supportsSeen.add(allSupport);
        let qb=0n;for(let si=0;si<splits.length;si++)if((allSupport>>si)&1)qb|=quartetContrib[si];
        const key=qb.toString();if(systems.has(key)){if(systems.get(key)!==allSupport)throw Error("Quartet system has unequal support");}else systems.set(key,allSupport);
      }
    }
    for(const [qstr,actualSupport] of systems){
      const qb=BigInt(qstr),rho4=new Map();
      for(let qi=0;qi<quartets.length;qi++){
        const Q=quartets[qi],qmask=Q.reduce((b,x)=>b|(1<<x),0);let qs=[];
        for(let t=0;t<3;t++)if(qb&(1n<<BigInt(3*qi+t)))qs.push((1<<Q[0])|(1<<Q[t+1]));
        if(qs.length<1||qs.length>2)throw Error("Invalid quartet support size");
        for(let ai=0;ai<4;ai++)for(let bi=ai+1;bi<4;bi++){const a=Q[ai],b=Q[bi];let separated=qs.filter(s=>!!(s&(1<<a))!==!!(s&(1<<b))).length;const val=4*separated/qs.length;if(!Number.isInteger(val))throw Error("Noninteger scaled rho");rho4.set(qmask+":"+a+":"+b,val);}
      }
      let positiveSupport=0;
      for(const [p,q] of pairs){
        const M=Array.from({length:n},()=>Array(n).fill(0));
        for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
          let v;if(a===p&&b===q)v=0;else if(a===p||a===q||b===p||b===q)v=2;
          else v=rho4.get(((1<<a)|(1<<b)|(1<<p)|(1<<q))+":"+a+":"+b);
          if(v===undefined)throw Error("Missing entry");
          M[a][b]=M[b][a]=v;
        }
        for(let si=0;si<splits.length;si++){const {i,j}=splits[si],a=i,b=i+1,c=j,d=(j+1)%n;const alpha=M[a][c]+M[b][d]-M[a][d]-M[b][c];checks++;if(alpha<0)negative++;if(alpha>0)positiveSupport|=1<<si;}
      }
      if(positiveSupport!==actualSupport)mismatches++;
      for(let si=0;si<splits.length;si++){
        const {i,j}=splits[si],a=i,b=i+1,c=j,d=(j+1)%n,Y=[...new Set([a,b,c,d])];let boundaryPresent;
        if(Y.length===3)boundaryPresent=true;else{
          const qi=quartets.findIndex(Q=>Y.every(x=>Q.includes(x))),Q=quartets[qi],wanted=(1<<b)|(1<<c),all=Y.reduce((z,x)=>z|(1<<x),0);
          const t=[0,1,2].find(t=>{const s=(1<<Q[0])|(1<<Q[t+1]);return s===wanted||s===(all^wanted);});
          if(t===undefined)throw Error("Missing boundary topology");
          boundaryPresent=!!(qb&(1n<<BigInt(3*qi+t)));
        }
        if(boundaryPresent!==!!((actualSupport>>si)&1))boundaryFailures++;
      }
    }
    const row={n,treeCases,selectedTrees,quartetSystems:systems.size,splitSystems:supportsSeen.size,anchorSplitChecks:checks,negative,supportMismatches:mismatches,boundaryFailures};
    results.push(row);report(row);
    if(negative||mismatches||boundaryFailures)throw Error("Verification failed");
  }
  return results;
}
const results = verifySupport(row => console.log(JSON.stringify(row)));
if (results.length !== 4) throw new Error('Missing size case');
