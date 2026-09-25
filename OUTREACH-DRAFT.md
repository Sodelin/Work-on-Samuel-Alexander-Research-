# Possible note to Samuel A. Alexander

This is a draft for the repository owner to edit and send. No message has been sent. Its links point to the intended public repository; check the [current status](STATUS.md) and [formalization receipt](verification/FORMALIZATION-RECEIPT.md) before sending if more work lands.

> Subject: A checked Thue–Morse follow-on and a specieslike question
>
> Dear Dr. Alexander,
>
> I enjoyed your video about the classification of biologically unavoidable sequences. It made me curious about what else the explicit avoiding graph can tell us, so I worked with Codex to put a [public, AI-assisted research notebook](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-) together. I would value your correction if we have missed a known result or misunderstood the model.
>
> The most concrete result is a [Lean-checked sharp bound](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/lean/SamuelAlexanderResearch/SharpThueMorse.lean) for the classification manuscript's Thue–Morse graph. If `L(v)` is the longest matching path from `v≥1`, then `3L(v)≤8v−1`. Equality occurs exactly at `v=3·2^n−1`, with `L(v)=8·2^n−3`. We checked the original graph's edges and the actual Thue–Morse bits in the formal development; the [scope and reproduction page](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/FORMALIZATION.md) explains what remains outside it.
>
> We also compared the avoiding graph with your inspecies and [specieslike-cluster](https://arxiv.org/html/2602.05274v1) work. Your 2013 Proposition 6 and 2026 Example 14 already cover the broad ancestry and root-cone patterns, and the [prior-work audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/PRIOR-WORK-AUDIT.md) credits them. The narrower observation is that the *same word-avoiding graph* has these specieslike properties; your earlier strictly layered cone example, if validly binary-labelled, realizes every binary word. A related [fixed-gender repair](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/notes/FIXED-GENDER-SPECIESLIKE.md) is written out but is not yet Lean checked.
>
> Is the sharp path formula familiar from another formulation? Or is the fixed-gender repair or the label-coverage boundary inside maximal common-ancestor clusters a more useful direction? There is no need to review the whole repository; the [brief handoff](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/HANDOFF-FOR-ALEXANDER.md) gives the exact statements and limits.
>
> Thank you for making the mathematics approachable in your videos.

## Short video outline if the owner wants to explain the work

1. **The setup:** distinguish an infinite graph with labelled parent edges from a prediction about real families. Credit Alexander's 2013 model and the later classification manuscript.
2. **The hook:** draw the Thue–Morse target and the two incoming edges at each numbered vertex. Show why the offset `d_k=v_k-2k` never increases along a matching path.
3. **The checked result:** state `3L(v)≤8v−1` for positive starts and show the exact equality family `v=3·2^n−1`; identify the Lean module and explain that the proof uses shrinking intervals of reachable endpoints and Thue–Morse bit identities.
4. **The source comparison:** credit the 2013 inspecies proposition and 2026 multiple-root example, then show why the earlier example's strict generations make every binary word realizable while the avoiding graph's skip edges change the path behavior.
5. **The invitation:** ask for an independent mathematical review or prior-art pointer; link the [handoff](HANDOFF-FOR-ALEXANDER.md), [audit](PRIOR-WORK-AUDIT.md), and exact [formalization scope](FORMALIZATION.md).

An optional second video can explain the [specieslike bridge](notes/SPECIESLIKE-BRIDGE.md): show why every vertex in `P_s` reaches all sufficiently later vertices, then distinguish the whole-graph cluster result from biological speciation and from the stronger common-ancestor condition.

The sharp path formula has a local Lean and agent review, while external mathematical review and literature priority remain open. The two-child fixed-gender question and any new cellular-automaton speed limit remain unsolved here. The [proof status table](STATUS.md) is the safest screen reference if the video is recorded after more results land.
