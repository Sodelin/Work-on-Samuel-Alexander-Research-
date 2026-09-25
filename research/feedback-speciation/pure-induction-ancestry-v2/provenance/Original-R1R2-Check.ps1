param([switch]$Run)
$ErrorActionPreference = 'Stop'
$ownDir = Split-Path -Parent $PSCommandPath
$parentDir = (Resolve-Path -LiteralPath (Join-Path $ownDir '..')).Path
$feedbackRoot = (Resolve-Path -LiteralPath (Join-Path $ownDir '..\..')).Path
$jointDir = Join-Path $parentDir 'lean'
$releaseDir = Join-Path $parentDir 'release\pure-induction-finite-v1'
$finiteRelease = Join-Path $feedbackRoot 'finite-epigenetic\release\finite-epigenetic-v1'
$finiteBuild = Join-Path $feedbackRoot 'finite-epigenetic\build'
$sourceFile = Join-Path $ownDir 'PureInductionR1R2.lean'
$outDir = Join-Path $ownDir 'build'
$outOlean = Join-Path $outDir 'PureInductionR1R2.olean'
$logFile = Join-Path $outDir 'PureInductionR1R2.log'
$packageRoot = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\real\.lake\packages'
$leanExe = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'

$release = Get-Content -LiteralPath (Join-Path $releaseDir 'MANIFEST.json') -Raw | ConvertFrom-Json
$jointEntry = @($release.files | Where-Object { $_.path -eq 'PureInductionJoint.lean' })
$jointReceipt = Get-Content -LiteralPath (Join-Path $jointDir 'CHECK-RECEIPT.json') -Raw | ConvertFrom-Json
if ($release.selectedNewEndpointCount -ne 4 -or $jointEntry.Count -ne 1 -or $jointReceipt.compilerExitCode -ne 0) {
  throw 'Frozen finite4 packet receipt mismatch.'
}
$jointSourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $jointDir 'PureInductionJoint.lean')).Hash.ToLowerInvariant()
$jointOleanHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $jointDir 'build\PureInductionJoint.olean')).Hash.ToLowerInvariant()
if ($jointSourceHash -ne $jointEntry[0].sha256 -or $jointSourceHash -ne $jointReceipt.sourceSha256 -or $jointOleanHash -ne $jointReceipt.oleanSha256) {
  throw 'Preserved finite4 source/object hash mismatch.'
}
$manifest = Get-Content -LiteralPath (Join-Path $finiteRelease 'MANIFEST.json') -Raw | ConvertFrom-Json
$receipt = Get-Content -LiteralPath (Join-Path $finiteRelease 'verification\combined-receipt.json') -Raw | ConvertFrom-Json
if ($manifest.checkedEndpointCount -ne 34 -or $receipt.selectedEndpointCount -ne 34) { throw 'Frozen 34 packet mismatch.' }
foreach ($module in @('FiniteFixation','FiniteEpigenetic','DeterministicEpigenetic','RankingReversal')) {
  $entry = @($manifest.files | Where-Object { $_.path -eq ($module + '.lean') })
  $checked = @($receipt.modules | Where-Object { $_.module -eq $module })
  if ($entry.Count -ne 1 -or $checked.Count -ne 1) { throw "Missing frozen dependency $module." }
  $sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $finiteRelease ($module + '.lean'))).Hash.ToLowerInvariant()
  $cacheHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $finiteBuild ($module + '.olean'))).Hash.ToLowerInvariant()
  if ($sourceHash -ne $entry[0].sha256 -or $cacheHash -ne $checked[0].oleanSha256) {
    throw "Frozen dependency mismatch $module."
  }
}
if (-not (Test-Path -LiteralPath $leanExe -PathType Leaf)) { throw 'Pinned Lean binary missing.' }
if (-not (Test-Path -LiteralPath $sourceFile -PathType Leaf)) { throw 'R1/R2 source missing.' }
$paths = @($outDir, (Join-Path $jointDir 'build'), $finiteBuild)
foreach ($package in Get-ChildItem -LiteralPath $packageRoot -Directory) {
  $libPath = Join-Path $package.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $libPath -PathType Container) { $paths += $libPath }
}
Write-Output 'Frozen finite4 and 34 sources/objects match receipts; isolated R1/R2 LEAN_PATH prepared.'
if (-not $Run) { Write-Output 'Preflight only; pass -Run for authorized compiler slot.'; return }
New-Item -ItemType Directory -Force -Path $outDir | Out-Null
$env:LEAN_PATH = ($paths -join ';')
& $leanExe -j1 -M4096 -o $outOlean $sourceFile 2>&1 | Tee-Object -FilePath $logFile
$code = $LASTEXITCODE
if ($code -ne 0) { throw "Lean failed exit $code; see $logFile" }
if (Select-String -LiteralPath $logFile -Pattern 'sorryAx|native_decide' -Quiet) {
  throw "Unexpected axiom marker in $logFile"
}
Get-FileHash -Algorithm SHA256 -LiteralPath $sourceFile,$outOlean,$logFile
Write-Output 'R1/R2 isolated check exit 0; inspect selected axiom lines.'


