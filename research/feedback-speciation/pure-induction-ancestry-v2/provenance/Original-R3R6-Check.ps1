param([switch]$Run, [ValidateSet('All','PureInductionNoise','PureInductionPaths','PureInductionAncestry')][string]$Module='All')
$ErrorActionPreference = 'Stop'
$proofDir = $PSScriptRoot
$bridgeDir = Split-Path -Parent $proofDir
$feedbackDir = Split-Path -Parent $bridgeDir
$taskPackages = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\real\.lake\packages'
$taskLeanExe = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'
$buildDir = Join-Path $proofDir 'build'
$verifyDir = Join-Path $proofDir 'verification'
$expectedR1Source = '633afd20f24da1c9cb86c5db7dda2bc1596b09cd634fe93ad0a70de0c5a8b85d'
$expectedR1Object = '3e1a6cadb94a51ffdfedad13bb2a0ed05a0508ba00074cbe6f4373ea6d5878b1'
function Get-ProofHash([string]$file) {
 (Get-FileHash -Algorithm SHA256 -LiteralPath $file).Hash.ToLowerInvariant()
}
if ((Get-ProofHash (Join-Path $bridgeDir 'r1-r2\PureInductionR1R2.lean')) -ne $expectedR1Source) { throw 'R1/R2 source changed from released worker handoff.' }
if ((Get-ProofHash (Join-Path $bridgeDir 'r1-r2\build\PureInductionR1R2.olean')) -ne $expectedR1Object) { throw 'R1/R2 object changed from released worker handoff.' }
& (Join-Path $bridgeDir 'r1-r2\Check.ps1')
$extDir = Join-Path $feedbackDir 'extinction'
$extReceipt = Get-Content -LiteralPath (Join-Path $extDir 'verification\receipt.json') -Raw | ConvertFrom-Json
if ($extReceipt.status -ne 'PASS') { throw 'Ancestry dependency receipt is not PASS.' }
$dependencies = @()
foreach ($entry in $extReceipt.modules) {
 $source = [IO.Path]::GetFullPath((Join-Path $extDir $entry.path))
 if ((Get-ProofHash $source) -ne $entry.sha256.ToLowerInvariant()) { throw "Ancestry dependency source changed: $source" }
 $dependencies += @{path=$source;sourceSha256=(Get-ProofHash $source)}
}
$mathlibDir = Join-Path $taskPackages 'mathlib'
$revision = (& git -c "safe.directory=$($mathlibDir -replace '\\','/')" -C $mathlibDir rev-parse HEAD | Out-String).Trim()
if ($revision -ne '0df444a360eaa60ab8c11dca51a86af692955474') { throw 'Pinned Mathlib revision mismatch.' }
$libPaths = @($buildDir, (Join-Path $bridgeDir 'r1-r2\build'), (Join-Path $bridgeDir 'lean\build'), (Join-Path $feedbackDir 'finite-epigenetic\build'), (Join-Path $extDir 'build'))
foreach ($pkg in Get-ChildItem -LiteralPath $taskPackages -Directory) {
 $lib = Join-Path $pkg.FullName '.lake\build\lib\lean'
 if (Test-Path -LiteralPath $lib -PathType Container) { $libPaths += $lib }
}
Write-Output 'R1/R2 object and sources match worker handoff; prior ancestry source and finite packets match receipts.'
if (-not $Run) { Write-Output 'Preflight only; no compiler started.'; return }
New-Item -ItemType Directory -Force -Path $buildDir,$verifyDir | Out-Null
$oldProofLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = $libPaths -join ';'
$modules = if ($Module -eq 'All') { @('PureInductionNoise','PureInductionPaths','PureInductionAncestry') } else { @($Module) }
try {
 foreach ($name in $modules) {
  $source = Join-Path $proofDir ($name+'.lean')
  $obj = Join-Path $buildDir ($name+'.olean')
  $log = Join-Path $verifyDir ($name+'.log')
  $sourceText = [IO.File]::ReadAllText($source)
  if ($sourceText -match '(?m)^\s*(axiom|constant)\s|\bsorry\b|\badmit\b|\bnative_decide\b') { throw "Unreviewed proof marker in $name." }
  $timer = [Diagnostics.Stopwatch]::StartNew()
  $result = (& $taskLeanExe -j1 -M4096 "--root=$proofDir" -o $obj $source 2>&1 | Out-String)
  $code = $LASTEXITCODE
  [IO.File]::WriteAllText($log,$result,[Text.UTF8Encoding]::new($false))
  Write-Output $result
  if ($code -ne 0) { throw "$name failed with compiler exit $code." }
  $audits = [regex]::Matches($result,"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
  $empty = [regex]::Matches($result,"'([^']+)' does not depend on any axioms")
  $wanted = [regex]::Matches($sourceText,'(?m)^\s*#print axioms\s+').Count
  if ($audits.Count+$empty.Count -ne $wanted -or $wanted -eq 0) { throw 'Selected axiom report count mismatch.' }
  $reports = @()
  foreach ($a in $audits) {
   $used = @($a.Groups[2].Value -split ',' | ForEach-Object {$_.Trim()} | Where-Object {$_})
   foreach ($v in $used) { if (@('propext','Classical.choice','Quot.sound') -notcontains $v) { throw "Unexpected axiom $v." } }
   $reports += @{declaration=$a.Groups[1].Value;axioms=$used}
  }
  foreach ($a in $empty) { $reports += @{declaration=$a.Groups[1].Value;axioms=@()} }
  $receipt = @{status='PASS';module=$name;compilerExitCode=$code;timestampUtc=[DateTime]::UtcNow.ToString('o');elapsedSeconds=$timer.Elapsed.TotalSeconds;lean='4.33.1';mathlibRevision=$revision;maximumWorkers=1;memoryLimitMb=4096;sourceSha256=(Get-ProofHash $source);oleanSha256=(Get-ProofHash $obj);logSha256=(Get-ProofHash $log);selectedEndpoints=$reports;reusedDependencies=$dependencies;dependencyMode='Existing checked local objects; no clean-machine rebuild in this run'}
  [IO.File]::WriteAllText((Join-Path $verifyDir ($name+'-receipt.json')),($receipt | ConvertTo-Json -Depth 12),[Text.UTF8Encoding]::new($false))
  Write-Output "$name PASS; $wanted selected axiom reports."
 }
} finally { $env:LEAN_PATH=$oldProofLeanPath }
