# Research progress — 25 September 2026

**Snapshot: 15:26 UTC / 08:26 Pacific.** This page makes the current work visible from the default branch. For mathematical status, follow the owning source ledger and exact verification receipt linked below.

## Start here

- **See the latest published research:** [draft PR #6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6).
- **Check its verified baseline:** [commit 138dd529](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/commit/138dd529643ae5706a9df6a750bd6344ab967a8a) and [successful hosted run](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36148288120).
- **Understand the questions:** [proof structure](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/PROOF-STRUCTURE.md) and [Wong coverage](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/wong/completion/COVERAGE.md).
- **See who owns the next result:** [research architecture and publication rules](RESEARCH-ARCHITECTURE.md).

The previous default README was last updated at 07:08 UTC. Later work was on the draft research branch. This front-page update exposes that work without implying that draft work has already been merged.

## What the work is teaching us

### 1. Simplifying ancestry while retaining the relationships we care about

An ancestral recombination graph describes which genome regions were inherited through which ancestors. Simplifying it should preserve the specified ancestry queries.

The new deterministic work separates three operations: removing ancestry above a local most recent common ancestor, contracting supported paths through nonsample unary nodes, and combining interval annotations into a canonical representation. Its practical contribution is an explicit account of what each operation preserves and what assumptions are needed.

**Evidence:** 24 MRCA, 31 interval and 10 normal-form declarations passed isolated local Lean checks. The final normal-form check finished at 15:23:27 UTC with exit 0 and only standard Lean axioms. These **65 declarations are awaiting combined library integration and hosted verification**; they are additional to the published 209-declaration real-library audit.

**Remaining:** stochastic-process obligations, continuous-time and spatial connections, executable-exporter obligations and the remaining coverage entries. Canonical interval storage being idempotent does not establish idempotence of the entire simplification pipeline. Whole Wong formalization remains unfinished.

### 2. Observations can preserve a prediction while losing a history

The published exact-abstraction result states when the information retained by an observation map is enough to predict the next observed state. The merge-history example shows how two states with the same current membership can still require different future answers when an operation depends on past parentage.

**Why it helps:** before connecting genetics, tissue states or social groups to a mathematical classification, we can ask precisely which distinctions the observation erased and whether those distinctions matter to the next query.

**Evidence:** the Q04 and Q09 modules are included in the linked successful hosted run. They settle restricted mathematical questions. **None of the twelve broad source questions is declared completely solved.** The [question ledger](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/138dd529643ae5706a9df6a750bd6344ab967a8a/research/open-problems/time-self-reference/problem-ledger.json) retains the remaining obligations.

### 3. A comparison can change when the model changes

The feedback/speciation owner has packaged a finite-versus-deterministic ranking example with 34 selected checked declarations. This is useful as a test of when conclusions from one population model can be transferred to another.

**Evidence boundary:** the local packet has observed successful exits for its finite component and final comparison. The interrupted deterministic component has a clean log and an object successfully imported by that final comparison; its original process exit was not recovered. Publication and portable integration remain pending.

This is a result inside specified mathematical models. It does not prove that DNA universally determines biological species or establish the intended connection to Alexander's infinite ancestry definitions. The Alexander lead is now isolating the exact transfer or obstruction.

## At a glance

| Work | Public status | Next concrete finish |
|---|---|---|
| Core, real and standalone research baseline | Published on PR #6; hosted pass at 138dd529: 405 core, 209 real, 129 standalone audited declarations | Preserve exact receipts as new work is integrated |
| Wong deterministic additions | 65 declarations locally checked; combined publication audit pending | Integrate MRCA + interval + normal form and update coverage |
| Wong count-process absorption | 2 scalar drift declarations checked; actual stochastic draft under development | Check the actual path law and absorption argument |
| Finite feedback ranking | 34-declaration local packet ready with the recorded exit-evidence qualification | Review, integrate and publish the packet |
| Same-prefix/noisy finite observations | Owner reports a completed 23-declaration local packet and interpretation review | Publish with exact scope and dependencies |
| Q10 order-convex Nash obstruction | Written construction, finite checks and a fresh Sol review; Astra adjudication pending | Check correspondence and publish the bounded claim |
| Broad connections | Source and theorem components available | One theorem with two explicit model applications |

Counts describe selected audited declarations, not independent discoveries. Passing Lean, usefulness and novelty are different judgments.

## What will appear next

1. A visible research architecture with three Astra Max leads, two shared Sol workers, one Luna assistant and the Astra auditor.
2. Public source packets and corresponding scope notes as each bounded review completes.
3. A worked example and an honest explanation of what each packet adds.
4. Commit-specific check results and the next unresolved obligation.

GitHub publication, author email and VibeMathed submission are distinct events. This update records GitHub progress; it is not a new email or site submission.
