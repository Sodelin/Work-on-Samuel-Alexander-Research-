# Portable research workflow

Use GitHub **main as the source of truth**. Chats are temporary workspaces; their uncommitted conclusions are proposals until the publication owner reviews and integrates them. Keep each continuation to one question and return a self-contained artifact so continuity does not depend on access to another chat.

## Set up once on main

The publication owner should place this document beside the research entry point and fill in:

- **Repository:** `https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-`
- **Entry point on main:** `CONTINUE-RESEARCH.md`
- **Active packet:** `research/continuation/NEXT-TASK.md`

The entry point should link to the current proof, independent audits, machine-readable receipts, and submission record. Existing files can serve these roles; a second archive is unnecessary. Each new chat records the exact main commit it read. If main changes during the work, report the base commit and return the result for integration rather than assuming the files are unchanged.

## Copy/paste kickoff prompt

```text
Continue this research from GitHub main:
Repository: https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-
Entry point: CONTINUE-RESEARCH.md
Packet: research/continuation/NEXT-TASK.md

Work noninteractively on this one packet. Read the entry point, the packet,
and only the proof/audit/source material needed for it. Record the exact main
commit and the files or public URLs you actually accessed. If an input is
inaccessible, say so; do not reconstruct its contents from a title or assume
that another chat's report is verified.

Follow the packet's scope, budget and stopping condition. Prioritize a proof,
counterexample, or precise missing lemma over broad exploration. Distinguish
external source claims, our candidate claims, evidence, and publication
status. Check the hypotheses and quantifiers of any cited result. Use primary
sources for mathematical attribution, with exact theorem/section locators.

Do not claim a test, enumeration, compiler, or proof-assistant check passed
unless you ran it and can provide its result. A receipt read from main is
inherited evidence, not a fresh run. A proof argument, exhaustive computation,
formal kernel check and external review are different kinds of evidence.

Return the output contract below as files/artifacts, a patch, or clearly
named file contents if artifact creation is unavailable. Preserve failed
attempts that explain a material limitation, briefly. Do not depend on another
chat messaging this one. Do not publish, submit, or update main; return the
proposal to the publication owner. Finish with the exact next action and
remaining blocker, if any. If clarification is essential, report the blocker
and complete any independent work within scope.
```

## One-question packet

Keep each packet short enough to paste alongside that prompt:

```text
ID/title:
Question: One precise proposition, counterexample search, or audit obligation.
Base: Exact commit SHA and relevant paths.
Inputs: Necessary proof sections, receipts, and primary-source locators.
Scope: Network/model class, observation type, hypotheses and quantifiers.
Deliverable: One proof note, counterexample, patch, or bounded audit.
Budget: Explicit search, case, or execution limit; no automatic expansion.
Stop when: Concrete success condition or documented obstruction.
Exclusions: Existing results or adjacent work owned elsewhere.
```

The current packet investigates global parameter-family circularity; the exact split-support argument already has a completed internal audit. “Solve all remaining identifiability problems” is too broad. The publication owner chooses the live packet using the latest main status.

## Required return

Every continuation returns **RESULT.md** containing:

1. Base commit, packet ID and verdict: proved under stated assumptions, counterexample, partial, or blocked.
2. Exact claim and argument, including any changed hypotheses; source links and theorem/section locators.
3. Evidence table: item, performed or inherited, result, and limitation.
4. Proposed changes, remaining obligation and one recommended next action.

Return **EVIDENCE.json** alongside it with `base_commit`, `packet_id`, `accessed_inputs`, `sources`, `checks_run`, `checks_not_run`, `artifacts`, and `submission_status`. Empty lists are valid; invented receipts are not.

- **With repository/execution tools:** also return changed files or a patch against the recorded base. For checks actually run, include the command, runtime/tool version when available, exit status and relevant output. Include hashes for computational certificates when practical. Keep edits inside the packet's allowed paths.
- **With browsing only:** return a source-grounded proof/audit note and the same evidence record. Mark local execution and formal checking as not performed. Provide proposed edits as named file contents or a patch only when the exact base text was accessible. An inability to execute does not prevent a useful mathematical argument.

The user can upload these files to the publication owner or paste their contents into the next chat. The owner reviews and integrates accepted work into main, then updates the entry point. A subsequent chat starts from that updated main commit.

## Status language that preserves the evidence

Maintain four separate facts: **source** (what an external paper states), **claim** (what we assert, with scope), **evidence** (what was checked and how), and **submission** (where a specific version was sent and its recorded outcome). A submission receipt is not mathematical acceptance; an internal audit is not publication or a Lean proof.

Starting context supplied on 29 September 2026: original all-level circularity and the local parameter domain have passed internal audits; the finite support check passed; the global support audit passed; full Lean verification is missing. Refresh these facts from main before using them. Do not preserve this snapshot as a permanent status claim. The publication owner controls main integration and VibeMath submissions.
