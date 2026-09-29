$ErrorActionPreference = 'Stop'
$dependencyRoot = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization'
$researchRoot = 'C:\Users\Owner\Documents\Alexander-Open-Questions-2026-09-29'
$leanPaths = @($PSScriptRoot, (Join-Path $researchRoot 'formal'), (Join-Path $researchRoot 'embedding'), (Join-Path $dependencyRoot '.lake\build\lib\lean'), (Join-Path $dependencyRoot 'real\.lake\build\lib\lean'))
foreach ($package in Get-ChildItem -LiteralPath (Join-Path $dependencyRoot 'real\.lake\packages') -Directory) {
  $library = Join-Path $package.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $library) { $leanPaths += $library }
}
$env:LEAN_PATH = $leanPaths -join ';'
$leanExe = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'
& $leanExe -o (Join-Path $PSScriptRoot 'BlowUpRankInvariance.olean') (Join-Path $PSScriptRoot 'BlowUpRankInvariance.lean') *> (Join-Path $PSScriptRoot 'BlowUpRankInvariance.log')
$code = $LASTEXITCODE
Get-Content -LiteralPath (Join-Path $PSScriptRoot 'BlowUpRankInvariance.log')
exit $code