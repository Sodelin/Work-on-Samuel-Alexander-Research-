# Continue this research from any capable chat

**Start here.** This repository is the durable home for the Alexander and
mathematical-biology work, including the new NANUQ theorem. The project aims
to develop formal methods that help people, with psychology and better care
as a long-term motivation. Each mathematical or practical claim still needs
its own stated assumptions and evidence; that motivation is not a claim that
biology or psychology has been solved.

Repository: <https://github.com/Sodelin/Work-on-Samuel-Alexander-Research->

1. Read [current status](research/continuation/CURRENT-STATUS.json).
2. Read the [active one-question packet](research/continuation/NEXT-TASK.md).
3. Follow the [portable workflow and return contract](research/continuation/WORKFLOW.md).
4. Return `RESULT.md` and `EVIDENCE.json`, plus any proposed source files or patch.

The research question, evidence and next action live in files. They do not
depend on another chat being able to message a running model. A chat that
cannot execute code can still return a proof, counterexample, source audit or
proposed Lean file, marked accurately as unexecuted. A later execution-capable
chat can check and integrate that contribution.

## Copy and paste into a new chat

```text
Continue the research at:
https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/CONTINUE-RESEARCH.md

Read that entry point, CURRENT-STATUS.json and NEXT-TASK.md. Work on the one
active packet noninteractively and within its stated bound. Read only the
necessary linked files and primary sources. Record the exact Git commit you
accessed; if you cannot resolve it or access a file, say so explicitly.

Try to prove the proposition or give an exact counterexample. Do not replace
the requested statement with an easier one without recording the change.
Return RESULT.md and EVIDENCE.json according to the linked workflow, with
any code as an artifact, patch, or clearly named file contents. Distinguish
checks you ran from receipts you read. Do not claim unrun Lean or Python
checks passed. Preserve a useful partial result and the precise remaining
obligation if the full packet is not solved. Do not rely on messaging other
chats. Stop at the packet's stopping condition and identify the next action.
```

To make a browsing-only handoff more reliable, download the packet and its
linked proof files at one commit and attach them together. To incorporate a
returned result, give those files to a chat with repository access and ask it
to review the exact claim, run the relevant checks, commit accepted changes,
update this status, and reconcile any existing submission before sending an
update. Submission authority comes from the user's instructions in that
session; a document never grants itself permission to contact people.

## Where the work is

| Work | Entry point | How to read its status |
|---|---|---|
| All-level NANUQ, exact split support, parameter family | [Current theorem package](research/nanuq-all-level-2026-09-29/README.md) | Computer-assisted proof with internal audits; full source theorem is not Lean formalized |
| Canonical-theta Lean proof and graph foundations from the other research chat | [Captured development](research/nanuq-all-level-2026-09-29/source-development/formal-full/ALL-LEVEL-QUALITY.md) | Read exact endpoints, logs, dated checkpoint and remaining obligations; older status notes remain historical |
| Alexander, ownership, finite sampling and earlier biology submissions | [Publication guide](PUBLICATION-GUIDE-2026-09-29.md), [coverage ledger](research/publication-2026-09-29/COVERAGE.md) | Follow pinned evidence and the submission manifest, not an old README's queue status |
| Psychology/social-science inventory and external-question audit | [Publication audit](research/publication-audit-2026-09-29/README.md) | The inventory distinguishes formal declarations from demonstrated answers to externally stated open problems |
| Extremal limits and side-chat refinements | [Register](research/nanuq-all-level-2026-09-29/source-development/extremality-sidechat/THEOREM-EXTREMALITY-REGISTER.md), [independent noise audit](research/nanuq-all-level-2026-09-29/EXTREMALITY-REPLAY.md) | 96 reference audit items; use the one active packet, not a new register-wide research queue |
| VibeMathed delivery | [Project manifest](PUBLIC-SUBMISSION-MANIFEST.json), [new theorem status](research/nanuq-all-level-2026-09-29/SUBMISSION-STATUS.json) | Prepared, submitted, under review, and accepted are separate states |

Prefer one bounded question and one integration owner. Independent audits
should challenge the proof or reproduce a check, rather than duplicate the
entire search. Save unsuccessful attempts only when they explain a real
obstruction. Completion never archives a chat; preserve the task and its history.

## New Wave review for future research

Apply the [New Wave protocol](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/main/NEW-WAVE.md): challenge the intended outcome, mechanism, actual restrictions, missing subsystems and potential transfer before registering a provisional target; then execute and verify it within the packet's budget. Attach any mathematical/significance delta and downstream-use evidence to the same packet. Read the [NANUQ experiment dossier](research/new-wave/NANUQ-EXPERIMENT-DOSSIER.md) for the historical basis and measurement limits. The [cross-project retrospective](https://github.com/Sodelin/Formalizing-Soft-Sciences/blob/main/research/new-wave-2026-09-30/RETROSPECTIVE.md) records the initial critique.

This supplements the current task contract. Preserve the active NANUQ packet and its stopping rules; do not replace it with an unrelated search. Record attempted strengthenings and unresolved limits even when the bounded packet ends with a partial result. Sol 6.1 is the preferred executor when available; effort is task-specific and the latest session preference is Medium. Report actual settings honestly.
