"use strict";
// Exact finite audit; no dependencies or file/network writes.
// Unbounded statements also require the mathematical proofs in PROOF-REFINEMENTS.md.

function symbolicRows(n,qb){
 const quads=[];for(let a=0;a<n;a++)for(let b=a+1;b<n;b++)for(let c=b+1;c<n;c++)for(let d=c+1;d<n;d++)quads.push([a,b,c,d]);
 const found=new Map();const zero=()=>[0,0,0,0,0];
 function gcd(a,b){while(b){const t=a%b;a=b;b=t;}return a;}
 for(let p=0;p<n;p++)for(let q=p+1;q<n;q++){
  function entry(u,v){if(u===v||(u===p&&v===q)||(u===q&&v===p))return zero();
   if(u===p||u===q||v===p||v===q)return [1,0,0,0,0];
   const qi=quads.findIndex(Q=>[u,v,p,q].every(x=>Q.includes(x))),Q=quads[qi],tops=[];
   for(let t=0;t<3;t++)if(qb&(1n<<BigInt(qi*3+t)))tops.push([Q[0],Q[t+1]]);
   if(tops.length===1){const same=tops[0].includes(u)===tops[0].includes(v);return same?[0,2,0,0,0]:[0,0,2,0,0];}
   if(tops.length!==2)throw Error("Unexpected quartet count");
   const gap=Math.abs(Q.indexOf(u)-Q.indexOf(v));return gap===2?[0,0,0,0,2]:[0,0,0,2,0];
  }
  for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
   const a=entry(i,j),b=entry(i+1,(j+1)%n),c=entry(i,(j+1)%n),d=entry(i+1,j);
   let v=a.map((x,k)=>x+b[k]-c[k]-d[k]),g=v.reduce((h,x)=>gcd(h,Math.abs(x)),0);if(!g)continue;v=v.map(x=>x/g);const key=v.join(",");
   if(!found.has(key))found.set(key,{row:v,quartetPattern:qb.toString(),anchors:[p,q],gaps:[i,j]});
  }
 }
 return found;
}

function verifySupport(report) {
  const results=[];
  function choose(n,k){const out=[];function rec(i,a){if(a.length===k){out.push(a);return;}for(;i<n;i++)rec(i+1,[...a,i]);}rec(0,[]);return out;}
  for(let n=3;n<=6;n++){
    const full=(1<<n)-1,pairs=choose(n,2),quartets=choose(n,4),splits=[],index=new Map();
    for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){let mask=0;for(let k=i+1;k<=j;k++)mask|=1<<k;let canonical=Math.min(mask,full^mask);index.set(canonical,splits.length);splits.push({i,j,mask:canonical});}
    const quartetContrib=splits.map(({mask})=>{let bits=0n;for(let qi=0;qi<quartets.length;qi++){const Q=quartets[qi];for(let t=0;t<3;t++){const left=(1<<Q[0])|(1<<Q[t+1]),right=Q.reduce((b,x)=>b|(1<<x),0)^left;if(((mask&left)===left&&(mask&right)===0)||((mask&right)===right&&(mask&left)===0))bits|=1n<<BigInt(3*qi+t);}}return bits;});
    let treeCases=0,selectedTrees=0,negative=0,mismatches=0,checks=0,boundaryFailures=0;let minSingleton=Infinity,minNontrivial=Infinity;const rowsFound=new Map();const systems=new Map(),supportsSeen=new Set();
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
      const qb=BigInt(qstr),rho4=new Map();for(const [k,w] of symbolicRows(n,qb))if(!rowsFound.has(k))rowsFound.set(k,w);
      for(let qi=0;qi<quartets.length;qi++){
        const Q=quartets[qi],qmask=Q.reduce((b,x)=>b|(1<<x),0);let qs=[];
        for(let t=0;t<3;t++)if(qb&(1n<<BigInt(3*qi+t)))qs.push((1<<Q[0])|(1<<Q[t+1]));
        if(qs.length<1||qs.length>2)throw Error("Invalid quartet support size");
        for(let ai=0;ai<4;ai++)for(let bi=ai+1;bi<4;bi++){const a=Q[ai],b=Q[bi];let separated=qs.filter(s=>!!(s&(1<<a))!==!!(s&(1<<b))).length;const val=4*separated/qs.length;if(!Number.isInteger(val))throw Error("Noninteger scaled rho");rho4.set(qmask+":"+a+":"+b,val);}
      }
      let positiveSupport=0;const totalAlpha=Array(splits.length).fill(0);
      for(const [p,q] of pairs){
        const M=Array.from({length:n},()=>Array(n).fill(0));
        for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
          let v;if(a===p&&b===q)v=0;else if(a===p||a===q||b===p||b===q)v=2;
          else v=rho4.get(((1<<a)|(1<<b)|(1<<p)|(1<<q))+":"+a+":"+b);
          if(v===undefined)throw Error("Missing entry");
          M[a][b]=M[b][a]=v;
        }
        for(let si=0;si<splits.length;si++){const {i,j}=splits[si],a=i,b=i+1,c=j,d=(j+1)%n;const alpha=M[a][c]+M[b][d]-M[a][d]-M[b][c];checks++;totalAlpha[si]+=alpha;if(alpha<0)negative++;if(alpha>0)positiveSupport|=1<<si;}
      }
      if(positiveSupport!==actualSupport)mismatches++;for(let si=0;si<splits.length;si++)if((actualSupport>>si)&1){const alpha=totalAlpha[si]/2;if(alpha<2)throw Error('Positive margin failed');let k=0;for(let x=0;x<n;x++)k+=(splits[si].mask>>x)&1;if(k===1||k===n-1){if(alpha<2*(n-2))throw Error('Singleton bound failed');minSingleton=Math.min(minSingleton,alpha);}else minNontrivial=Math.min(minNontrivial,alpha);}
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
    const row={n,treeCases,selectedTrees,quartetSystems:systems.size,splitSystems:supportsSeen.size,anchorSplitChecks:checks,negative,supportMismatches:mismatches,boundaryFailures,minSingletonAlpha:minSingleton,minNontrivialAlpha:Number.isFinite(minNontrivial)?minNontrivial:null,symbolicRows:[...rowsFound.values()].sort((a,b)=>(a.row.join(',') < b.row.join(',') ? -1 : a.row.join(',') > b.row.join(',') ? 1 : 0))};
    results.push(row);report(row);
    if(negative||mismatches||boundaryFailures)throw Error("Verification failed");
  }
  return results;
}

function verifyRefinements(rows){
 function requireTrue(x,msg){if(!x)throw Error(msg);}
 function matrix(topologies){const D=Array.from({length:4},()=>Array(4).fill(0));for(let a=0;a<4;a++)for(let b=a+1;b<4;b++){const sep=topologies.filter(A=>A.includes(a)!==A.includes(b)).length;D[a][b]=D[b][a]=4+2*sep/topologies.length;}return D;}
 function coefficient(D,i,j){return D[i][j]+D[i+1][(j+1)%4]-D[i][(j+1)%4]-D[i+1][j];}
 const tree=matrix([[0,1]]),cycle=matrix([[0,1],[0,3]]);
 requireTrue(tree.flat().every(Number.isInteger)&&cycle.flat().every(Number.isInteger),"Source integrality");
 let norm=0;const midpoint=tree.map((r,i)=>r.map((x,j)=>{norm=Math.max(norm,Math.abs(x-cycle[i][j]));return (x+cycle[i][j])/2;}));
 requireTrue(norm===1,"Sharp-radius witness norm");
 requireTrue(coefficient(tree,0,2)===0&&coefficient(cycle,0,2)===2,"Distinct support at common circular order");
 requireTrue(tree.flat().every((x,k)=>Math.abs(x-midpoint.flat()[k])<=0.5)&&cycle.flat().every((x,k)=>Math.abs(x-midpoint.flat()[k])<=0.5),"Midpoint ambiguity");
 for(let x=-10;x<=100;x++)for(const e of [-0.49,-0.25,0,0.25,0.49])requireTrue(Math.round(x+e)===x,"Rounding sanity check");
 const R=rows.map(r=>new Set(r.symbolicRows.map(w=>w.row.join(","))));
 requireTrue(R[1].size===10&&R[2].size===16&&R[3].size===16,"Row catalog cardinalities");
 requireTrue([...R[3]].every(v=>R[2].has(v))&&[...R[2]].every(v=>R[3].has(v)),"Five/six catalog equality");
 const outside=[1,0,1,0.25,1];
 const evalRow=w=>w.row.reduce((z,x,i)=>z+x*outside[i],0);
 requireTrue(rows[1].symbolicRows.every(w=>evalRow(w)>=0),"Four-label parameter witness");
 const neg=rows[2].symbolicRows.filter(w=>evalRow(w)<0);
 requireTrue(neg.length>0,"Five-label witness must fail");
 const pairRows=[];
 for(const g of [{name:"absent",tops:[[0,1]],tau:0},{name:"unique",tops:[[1,2]],tau:2},{name:"both",tops:[[0,1],[1,2]],tau:1}]){
  for(let p=0;p<4;p++)for(let q=p+1;q<4;q++){
   function M(u,v){if(u===v||(u===p&&v===q)||(u===q&&v===p))return 0;if(u===p||u===q||v===p||v===q)return 1;return 2*g.tops.filter(A=>A.includes(u)!==A.includes(v)).length/g.tops.length;}
   const alpha=M(0,2)+M(1,3)-M(0,3)-M(1,2),expected=((p===0&&q===3)||(p===1&&q===2))?g.tau:0;
   requireTrue(alpha===expected,"Boundary anchor identity");pairRows.push({case:g.name,anchors:[p,q],alpha});
  }
 }
 // Physical occurrence tree: a is pendant root; rest is ((b,(c0,d0)),(c1,d1)).
 const intervals=[[1,5],[1,3],[1,1],[2,3],[2,2],[3,3],[4,5],[4,4],[5,5]],topologies=new Set(),selections=[];
 for(const c of [2,4])for(const d of [3,5]){
  const selected=[0,1,c,d];let topology=null;
  for(const [lo,hi]of intervals){let mask=0;for(let x=0;x<4;x++)if(selected[x]>=lo&&selected[x]<=hi)mask|=1<<x;
   if(mask===3||mask===12)topology="ab|cd";else if(mask===5||mask===10)topology="ac|bd";else if(mask===9||mask===6)topology="ad|bc";
  }
  requireTrue(topology!==null,"Missing selected topology");topologies.add(topology);selections.push({cOccurrence:c,dOccurrence:d,topology});
 }
 requireTrue(topologies.size===3,"Non-outer counterexample support");
 // Exact numerator in denominator 3: d=4+2*(2/3)=16/3.
 const equilateralTimes3=Array.from({length:4},(_,i)=>Array.from({length:4},(_,j)=>i===j?0:16));
 requireTrue(coefficient(equilateralTimes3,0,2)===0&&coefficient(equilateralTimes3,1,3)===0,"Counterexample star support");
 return {
  boundaryAnchorIdentities:{passed:true,cases:pairRows},
  symbolicCatalogue:{fiveEqualsSix:true,minimumLabelsForThisCatalogue:5,structuralFiveLabelReduction:"OPEN",newRowsAtFive:[...R[2]].filter(v=>!R[1].has(v)),parameterCounterexample:{coordinates:["constant","c","s","a","o"],values:outside,passesEveryFourLabelRow:true,negativeFiveLabelRows:neg}},
  sharpNoiseRadius:{radiusNumerator:1,radiusDenominator:2,strictInequalityRequired:true,treeMatrix:tree,cycleMatrix:cycle,midpoint,supNormDifference:norm,status:"Analytic proof plus exact endpoint witness; applies to raw unnormalized original NANUQ, correct circular order supplied for support extraction."},
  nonOuterCounterexample:{selections,distinctTopologies:[...topologies],distanceTimes3:equilateralTimes3,nontrivialSplitCoefficientsTimes3:0,status:"Graph-class admission is justified in PROOF-REFINEMENTS.md; this code verifies its occurrence selections and metric."}
 };
}

function runAudit() {
  const support = verifySupport(() => {});
  const refinements = verifyRefinements(support);
  return {schemaVersion:1,verification:"Exact finite JavaScript execution, not Lean",support,refinements};
}

console.log(JSON.stringify(runAudit(), null, 2));
