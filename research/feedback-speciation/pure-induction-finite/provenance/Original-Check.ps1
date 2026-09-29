param([switch]$Run)
$ErrorActionPreference = 'Stop'

$ownDir = Split-Path -Parent $PSCommandPath
$feedbackRoot = (Resolve-Path -LiteralPath (Join-Path $ownDir '..\..')).Path
$releaseDir = Join-Path $feedbackRoot 'finite-epigenetic\release\finite-epigenetic-v1'
$baseBuild = Join-Path $feedbackRoot 'finite-epigenetic\build'
$sourceFile = Join-Path $ownDir 'PureInductionJoint.lean'
$outDir = Join-Path $ownDir 'build'
$outOlean = Join-Path $outDir 'PureInductionJoint.olean'
$logFile = Join-Path $outDir 'PureInductionJoint.log'
$packageRoot = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\real\.lake\packages'
$leanExe = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'

$manifest = Get-Content -LiteralPath (Join-Path $releaseDir 'MANIFEST.json') -Raw | ConvertFrom-Json
$receipt = Get-Content -LiteralPath (Join-Path $releaseDir 'verification\combined-receipt.json') -Raw | ConvertFrom-Json
if ($manifest.checkedEndpointCount -ne 34 -or $receipt.selectedEndpointCount -ne 34) {
  throw 'Frozen 34-endpoint receipt did not match expected packet.'
}
foreach ($module in @('FiniteFixation','FiniteEpigenetic','DeterministicEpigenetic','RankingReversal')) {
  $name = $module + '.lean'
  $entry = @($manifest.files | Where-Object { $_.path -eq $name })
  $checked = @($receipt.modules | Where-Object { $_.module -eq $module })
  if ($entry.Count -ne 1 -or $checked.Count -ne 1) { throw "Missing manifest entry for $module." }
  $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $releaseDir $name)).Hash.ToLowerInvariant()
  $cacheHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $baseBuild ($module + '.olean'))).Hash.ToLowerInvariant()
  if ($sourceHash -ne $entry[0].sha256 -or $cacheHash -ne $checked[0].oleanSha256) {
    throw "Frozen source or compiled cache mismatch for $module."
  }
}
if (-not (Test-Path -LiteralPath $leanExe -PathType Leaf)) { throw 'Pinned Lean executable missing.' }
if (-not (Test-Path -LiteralPath $sourceFile -PathType Leaf)) { throw 'Owned source file missing.' }

$paths = @($outDir, $baseBuild)
foreach ($package in Get-ChildItem -LiteralPath $packageRoot -Directory) {
  $libPath = Join-Path $package.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $libPath -PathType Container) { $paths += $libPath }
}
$mathlibPath = Join-Path $packageRoot 'mathlib\.lake\build\lib\lean'
if (-not (Test-Path -LiteralPath (Join-Path $mathlibPath 'Mathlib\Tactic\FinCases.olean') -PathType Leaf)) {
  throw 'Pinned FinCases cache missing.'
}

Write-Output "Frozen source and four compiled artifacts match the 34-endpoint receipt."
Write-Output "Prepared isolated output: $outDir"
if (-not $Run) {
  Write-Output 'Preflight only. Compiler not launched; pass -Run only after root grants the compiler slot.'
  return
}

New-Item -ItemType Directory -Force -Path $outDir | Out-Null
$env:LEAN_PATH = ($paths -join ';')
& $leanExe -j1 -M4096 -o $outOlean $sourceFile 2>&1 | Tee-Object -FilePath $logFile
$code = $LASTEXITCODE
if ($code -ne 0) { throw "Lean failed with exit code $code. See $logFile" }
if (Select-String -LiteralPath $logFile -Pattern 'sorryAx|native_decide' -Quiet) {
  throw "Unexpected axiom or native_decide marker in $logFile"
}
Get-FileHash -Algorithm SHA256 -LiteralPath $sourceFile, $outOlean, $logFile
Write-Output 'Isolated PureInductionJoint Lean check completed; inspect printed axiom sets in the log.'
