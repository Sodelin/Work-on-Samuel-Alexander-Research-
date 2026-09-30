# An interval-partition route to anchor positivity

2026-09-29. Optional human-proof supplement. The main composition proof can instead use the separately audited finite compression and exact enumeration. The general interval lemma below is proved here. Its application to every canonical theta is a proposed structural proof for independent review, not a replacement for the already specified computer-assisted certificate until audited.

Fix two anchors p,q in a circularly ordered taxon set. In every displayed tree, remove the p-q path. The non-anchor taxa fall into the components attached off this path. Each component is an interval on one of the two open p-q arcs. Two non-anchor leaves x,y belong to the same component if and only if the tree displays pq|xy.

For a family of outer-planar displayed trees, call x,y forced together when they share a component in every tree. This is an equivalence relation; its classes F are intervals. Every possible off-path component is a union of these classes. Let C be the family of inclusion-maximal possible components.

## General interval lemma

Assume the intersection of any two distinct maximal possible components is either empty or a single forced class. Then the anchor matrix M, defined by M(p,q)=0, M(p,x)=M(q,x)=1, and M(x,y)=2 rho_xy(N|xypq) otherwise, has the circular split decomposition

  M = (1/2) sum_{C maximal possible component} delta_C
      + sum_{F forced class} (1-c(F)/2) delta_F,

where c(F) is the number of maximal possible components containing F; the anchors lie outside every displayed split side in this formula.

Proof. After contracting forced classes, maximal possible components form an antichain of intervals on each open anchor arc. Their pairwise intersections have at most one contracted point. Such an interval antichain has each point in at most two intervals: if three intervals contain a point and their left endpoints are increasing, their right endpoints also increase; the first and second then overlap in the point and at least the second interval's distinct left endpoint, a contradiction. Thus c(F)<=2 and every coefficient in the displayed decomposition is nonnegative.

Each non-anchor x lies in one forced class F. The total weight of split sides containing x is c(F)/2+(1-c(F)/2)=1. This proves its distance from each anchor is 1. For x,y in the same forced class, the containing sides coincide and the distance is 0. For distinct forced classes that can occur together, exactly one maximal possible component contains both, so their distance is 2-2(1/2)=1. If they never occur together, no split side contains both, and their distance is 2.

These are exactly the entries of the anchor matrix. Outer-planarity allows only two noncrossing quartet topologies on any fixed four cyclically ordered taxa. Thus a pair is always a cherry relative to the anchors, sometimes a cherry, or never a cherry, with uniform-distinct separation indicator 0,1/2,1 respectively. The displayed formula follows. All split sides are circular intervals, completing the proof.

This lemma proves only nonnegativity, which is enough: the main proof's anchor expansion plus the published unit-mass exact-support theorem supplies the support for all positive terminal masses.

## Application proposed for canonical level-two theta bloblets

Delete the two hybrid leaves C1,C2 and their attachment vertices, retaining the ordinary backbone S and the attachment sites. The backbone has adjacent junctions u,v, with arms A1,A2 from u and B1,B2 from v. The two hybrid leaves move independently between the terminal attachment sites of Ai and Bi. Empty arms identify the corresponding site with its junction. This keeps the argument applicable to degenerate arm counts.

Case 1: both anchors are ordinary leaves. Their backbone path is fixed in all four switchings. Its off-path backbone components D are fixed, and ordinary taxa in each D are forced together. A hybrid joins D exactly when its chosen attachment site lies there; if its attachment lies on the anchor path it instead forms a singleton component. The maximal possible components are obtained from D by adding every hybrid with an attachment site in D, followed by deleting nonmaximal sets; components with no ordinary taxa and isolated hybrid singletons are included by the same description.

Distinct D,E cannot both receive both hybrids. If they did, the two attachment sites for each hybrid would be split between D and E. Up to exchanging the component names, either D connects A1 with A2 and E connects B1 with B2, or D connects A1 with B2 and E connects B1 with A2. In the first case D contains u and E contains v, but the edge uv is disjoint from the removed anchor path and joins them, contradicting distinctness. In the second case both components contain u and v, again impossible. Therefore maximal possible components intersect in at most one hybrid. Any such hybrid is a singleton forced class unless it always stays with ordinary taxa; in that latter situation those ordinary taxa would belong to both maximal components as well, which is impossible. The interval lemma applies.

Case 2: exactly one anchor, say C1, is hybrid. Let a,b be its two attachment sites and let q be the ordinary anchor. The two possible anchor paths in S form a Y, possibly with one arm of length zero. Their common stem runs from q to the branch point. The maximal possible sets of ordinary off-path taxa are: the components attached along the common stem, and the two branches toward a and b that can be omitted by choosing the other attachment. They are disjoint and partition the non-anchor ordinary taxa. Components along an included arm are smaller subsets of its omitted-arm component.

The other hybrid C2 is free to choose either of its attachment sites independently of the anchor choice. If it can join a smaller ordinary component within an arm, the switching omitting that arm lets it join the corresponding maximal ordinary component at the same attachment site. Hence no smaller augmented component creates a new crossing maximal block. Maximal possible components consist of the disjoint maximal ordinary sets, optionally augmented by C2, and any necessary singleton C2. Their only possible overlap is C2 itself. The interval lemma applies. A careful graph audit should explicitly include attachment sites at the Y branch point and the degenerate-Y case.

Case 3: both anchors are hybrid. The four backbone anchor paths join one of A1/B1 to one of A2/B2. The maximal possible ordinary off-path sets are A1 union A2, and B1 union B2, omitting empty sets. They are disjoint: the switching through v omits the u side, and the switching through u omits the v side. Every other off-path component is contained in one of these two sets. The interval lemma applies directly.

This proposed classification is consistent with the parent's exhaustive small-template checks and would give a short purely structural alternative to their finite reduction. The composition identity in COMPOSITION-PROOF.md does not depend on accepting this optional classification; it needs only the local anchor-positivity conclusion established by either audited route.