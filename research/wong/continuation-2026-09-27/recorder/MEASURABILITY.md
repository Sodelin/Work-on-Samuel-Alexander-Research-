# Full marked-state Borel measurability

Implementation: `real/WongMarkedMeasurable.lean`. Compiled PASS in 29.585 seconds; 17 project modules in the requested import closure. Selected printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Full warnings and exact source/object hashes are retained in `MEASURABILITY-VERIFICATION.json`, `measurability-module-receipt.json`, and `measurability-compiler.log`. Final combined commit verification is a separate integration step.

The sigma algebra is fixed by the data representation before mentioning a process or law. It is built from ordinary real Borel coordinates, discrete natural/Boolean/finite-natural-set coordinates, and countable products:

| Stored type | Faithful code |
|---|---|
| Proper interval | Pair of real endpoints; the proof of strict order carries no extra data |
| Lineage slot | Natural child vertex and interval code |
| Event kind | Boolean split flag plus real cut, with a fixed zero in the merger case |
| Raw event | Fresh natural vertex, event kind, consumed-ID set and allocated-ID set |
| Event list | Natural length plus the sequence of nth events, padded with one fixed default event |
| Raw recorder state | Two natural counters, complete slot sequence, parent sequence, active-ID set and complete event list |
| Optional raw state | Presence Boolean and the state, padded by one fixed initial state on absence |

Each encoder has a checked injectivity statement in the module. These pullback sigma algebras therefore retain all the raw data. In particular they neither assign every subset of the uncountable real-cut space to be measurable nor choose a sigma algebra tailored to make the final process measurable by definition.

The substantive proof is that the actual update is measurable. Fresh-ID allocation, finite set operations and membership guards are discrete. Cut endpoints enter through measurable real coordinates. Dynamic evaluation of a slot sequence or innovation row uses a countable index and its product sigma algebra. Event append is proved measurable using the explicit padded nth-event formula.

`measurable_step` treats the actual `WongMarkedProcess.step`, including its failure branches and proof-dependent interior cuts. `measurable_recordPrefix_of_coordinates` proves the actual recursion measurable using only counts through t and innovation rows before t. It does not assume the entire input is measurable or assume future innovations are available in the past sigma algebra. This is the interface for the separate adaptive-uniformity proof.

`measurable_stoppedRecord` uses measurable firstHit and countable dynamic selection of the fixed-prefix maps. This proves measurability of the entire stopped raw graph/event object, not just its count and time observables. `stoppedRecordLaw` is its actual pushforward measure and `stoppedRecordLaw_probability` supplies the probability-measure instance.

The deterministic decoder/graph adapter remains unchanged. The raw stopped object retains enough information to recover its finite graph and raw event metadata by those constructions. The structural sigma algebra does not itself assert source correspondence, biological species identification, or an adaptive conditional law; those are separate statements in the coordinating source/transition ledger.

