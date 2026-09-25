param([string]$File = 'ThreeTaxonFiniteEvidence.lean')
$ErrorActionPreference = 'Stop'
$taskSourceRoot = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization'
$taskLeanPaths = @($PSScriptRoot)
foreach ($taskPackage in Get-ChildItem -LiteralPath (Join-Path $taskSourceRoot 'real\.lake\packages') -Directory) {
  $taskLibrary = Join-Path $taskPackage.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $taskLibrary) { $taskLeanPaths += $taskLibrary }
}
$env:LEAN_PATH = $taskLeanPaths -join ';'
& 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' (Join-Path $PSScriptRoot $File)
exit $LASTEXITCODE
