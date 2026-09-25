# Possible note to Samuel A. Alexander

This is a draft for the repository owner to edit and send. No message has been sent. It describes the current state accurately; revise it if a later theorem, formalization, or independent review changes that state.

> Subject: Follow-on questions from biologically unavoidable sequences
>
> Dear Dr. Alexander,
>
> I enjoyed your video about the classification of biologically unavoidable sequences and wanted to see whether its construction could lead to more small, checkable problems. I worked with Codex to put a public follow-on research notebook here: [Working on Samuel Alexander's research](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-).
>
> One direction studies how long the Thue-Morse sequence can be matched in the classification paper's explicit avoiding population. The notebook gives a written quadratic upper bound using the classical overlap-free property, along with exact code that suggests a much sharper linear bound. The linear bound is still a conjecture; I would not want the computation to be mistaken for a proof. We also noticed a direct connection to your recent [specieslike-clusters paper](https://arxiv.org/html/2602.05274v1): the whole binary avoiding graph satisfies its basic cluster axioms after parent labels are ignored. The short [written argument](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/notes/SPECIESLIKE-BRIDGE.md) states exactly which stronger cluster conditions it does not address.
>
> If either direction connects to a question you find interesting, I would be glad to hear which is worth pursuing. Corrections or pointers to prior work would be especially welcome. There is no need to review the whole repository; the [brief handoff](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/HANDOFF-FOR-ALEXANDER.md) and [research map](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/RESEARCH-MAP.md) give short entry points.
>
> Thank you for making the mathematics approachable in your videos.

## Short video outline if the owner wants to explain the work

1. **The setup:** distinguish an infinite graph with labelled parent edges from a prediction about real families. Credit Alexander's 2013 model and the later classification manuscript.
2. **The hook:** draw the Thue–Morse target and the two incoming edges at each numbered vertex. Show why the offset `d_k=v_k-2k` never increases along a matching path.
3. **The proved extension:** explain in words why overlap-freeness limits how long the path can remain at one offset, giving a quadratic upper bound.
4. **The puzzle:** show the finite path-length data and the proposed linear formula. Label it "conjecture, checked for starts below 131072" on screen.
5. **The invitation:** ask for a proof, counterexample, or prior-art pointer; link the repository's exact model, code, and status page.

An optional second video can explain the [specieslike bridge](notes/SPECIESLIKE-BRIDGE.md): show why every vertex in `P_s` reaches all sufficiently later vertices, then distinguish the whole-graph cluster result from biological speciation and from the stronger common-ancestor condition.

Do not present the linear formula, the two-child fixed-gender question, or a new cellular-automaton speed limit as solved. An independently checked proof would justify a stronger follow-up video.
