// Standalone finite sanity checks for the endpoint-coverage equivalence.
// Run with: node endpoint-coverage-check.js
// This finite check is not a Lean proof or verification of Wong's model.
function runEndpointCoverageAudit() {
  const lo = 0, hi = 8;
  const contains = (interval, x) => interval[0] <= x && x < interval[1];
  const exact = (intervals, x) => intervals.reduce((n, I) => n + Number(contains(I, x)), 0) === 1;
  const endpoints = intervals => [...new Set([lo, hi, ...intervals.flat()])].sort((a,b) => a-b);
  let checked = 0, comparisons = 0;
  function check(intervals) {
    const E = endpoints(intervals);
    const probes = E.filter(x => lo <= x && x < hi);
    const cells = E.slice(0,-1).map((a,i) => (a+E[i+1])/2).filter(x => lo <= x && x < hi);
    const atEndpoints = probes.every(x => exact(intervals,x));
    const acrossCells = [...probes,...cells].every(x => exact(intervals,x));
    if (atEndpoints !== acrossCells) throw new Error("Endpoint equivalence failed");
    for (const x of [...probes,...cells]) {
      const y = Math.max(...E.filter(e => e <= x));
      if (!(lo <= y && y <= x && y < hi)) throw new Error("Floor bound failed");
      for (const I of intervals) {
        comparisons++;
        if (contains(I,x) !== contains(I,y)) throw new Error("Membership preservation failed");
      }
    }
    checked++;
    return atEndpoints;
  }
  const grid=[0,2,4,6,8], choices=[];
  for (let i=0;i<grid.length;i++) for (let j=i+1;j<grid.length;j++) choices.push([grid[i],grid[j]]);
  function enumerate(prefix,remaining) {
    check(prefix);
    if (remaining>0) for (const I of choices) enumerate([...prefix,I],remaining-1);
  }
  enumerate([],4);
  const exhaustiveFamilies=checked;
  if (!check([[0,4],[4,8]])) throw new Error("Adjacent partition rejected");
  if (check([[0,8],[0,8]])) throw new Error("Distinct duplicate slots were collapsed");
  if (check([[0,2],[6,8]])) throw new Error("Gap accepted");
  if (check([[0,6],[2,8]])) throw new Error("Overlap accepted");
  if (!check([[-2,2],[2,10]])) throw new Error("External endpoints mishandled");
  if (check([])) throw new Error("Empty frontier accepted");
  const gap=[[0,2],[6,8]];
  if (!gap.map(I=>I[0]).every(x=>exact(gap,x))) throw new Error("Left-endpoint canary not demonstrated");
  return {
    status:"PASS_FINITE_SANITY_CHECK_ONLY",
    exhaustiveFamilies,
    additionalBoundaryCases:checked-exhaustiveFamilies,
    totalFamilies:checked,
    slotMembershipComparisons:comparisons,
    genome:"[0,8)",
    enumeration:"All ordered lists of at most four intervals from the ten proper intervals on {0,2,4,6,8}; repeated intervals retain distinct slot identities.",
    canary:"Testing only left endpoints misses the gap in [0,2), [6,8).",
    scope:"Independent endpoint/cell and membership sanity checks. Not Lean verification; not a check of the main repository."
  };
}
if (typeof module !== "undefined") module.exports = {runEndpointCoverageAudit};
if (typeof require !== "undefined" && require.main === module) console.log(JSON.stringify(runEndpointCoverageAudit(),null,2));

