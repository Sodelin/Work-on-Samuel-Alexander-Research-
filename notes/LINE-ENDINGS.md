# Saved repository line-ending fix

Prepared on 25 September 2026 for `Sodelin/Work-on-Samuel-Alexander-Research-`.

The complete two-file change is saved in [line-ending-fix.patch](../patches/line-ending-fix.patch). It updates `.gitattributes` and adds `.editorconfig`.

## Policy

- Automatically detected text uses LF endings in Git and on checkout, including Markdown, Python and configuration files.
- Lean files remain explicitly marked as text with LF endings.
- Windows `.bat` and `.cmd` scripts use CRLF on checkout.
- PDF, PNG, JPEG, GIF, gzip, ZIP and Lean `.olean` artifacts are explicitly binary and exempt from line-ending conversion.
- Editors supporting EditorConfig use UTF-8, LF and a final newline, with the batch-script exception above. The settings do not remove trailing spaces, including Markdown hard breaks.

The computer's existing system Git setting is `core.autocrlf=true`. The fix is scoped to this repository through versioned attributes; no global Git setting was changed.

## Apply

From a checkout still containing the original one-line `.gitattributes` and no `.editorconfig`, check and apply the saved patch:

```powershell
git apply --check "PATH/TO/line-ending-fix.patch"
git apply "PATH/TO/line-ending-fix.patch"
```

The first command only checks applicability. It passed against the current implementation checkout before handoff. Once this fix is committed and pulled normally, applying this patch again is unnecessary.

## Verification and limits

Git's `check-attr` confirmed LF for representative Lean, Markdown, Python and workflow files, CRLF for a batch-script path, and disabled text conversion for binary paths. The root checkout's index already contains 123 LF text blobs and one binary gzip blob, so this baseline needs no blanket renormalization. Some existing working-tree files still have CRLF; merely adding attributes does not rewrite those files immediately. Future checkouts and supported editor saves apply the policy.

A separate read-only reviewer found the policy consistent with the tracked file types. No broad staging, reset, deletion, renormalization, or proof-source edit was performed as part of this change. LaTeX syntax and rendering remain covered by the separate math checks.

| Artifact | SHA-256 |
| --- | --- |
| Patch | `db76c0370bac464ef3813df6b6f3e919016a53cda05874ee611c04ef69ea7285` |
| New `.gitattributes` | `a32da5d4c03ab902f3a7982dee8f87f60c8d498ebfab53a652afdb5d5e5ed0f9` |
| New `.editorconfig` | `3f98ae7d1a00751db3e32bdb4b2b3f53df8417d08946469bae79db6fb6e15334` |

Reference: [Git's official attributes documentation](https://git-scm.com/docs/gitattributes).
