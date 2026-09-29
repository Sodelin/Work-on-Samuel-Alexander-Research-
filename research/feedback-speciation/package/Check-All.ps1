param(
  [Parameter(Mandatory=$true)][string]$MathlibPackages,
  [string]$LeanExe = 'lean'
)
$ErrorActionPreference='Stop'
$packageRoot=$PSScriptRoot
$expectedMathlib='0df444a360eaa60ab8c11dca51a86af692955474'
$mathlibRoot=Join-Path $MathlibPackages 'mathlib'
$actualMathlib=(& git -c "safe.directory=$($mathlibRoot -replace '\\','/')" -C $mathlibRoot rev-parse HEAD | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $actualMathlib -ne $expectedMathlib) { throw 'Mathlib revision mismatch' }
$leanVersion=(& $LeanExe --version | Out-String).Trim()
if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch 'version 4\.33\.1\b') { throw 'Lean 4.33.1 required' }
$buildRoot=Join-Path $packageRoot 'build'
$logRoot=Join-Path $packageRoot 'verification'
New-Item -ItemType Directory -Force -Path $buildRoot,$logRoot | Out-Null
$libraryPaths=@($buildRoot)
foreach ($dependency in Get-ChildItem -LiteralPath $MathlibPackages -Directory) {
  $library=Join-Path $dependency.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $library) { $libraryPaths += $library }
}
$previousLeanPath=$env:LEAN_PATH
$env:LEAN_PATH=$libraryPaths -join [IO.Path]::PathSeparator
$modules=@(
  @{Path='vendor/SamuelAlexanderResearch/SpeciesBridge.lean'; Module='SamuelAlexanderResearch/SpeciesBridge'},
  @{Path='vendor/SamuelAlexanderResearch/SpeciesGlobalIAP.lean'; Module='SamuelAlexanderResearch/SpeciesGlobalIAP'},
  @{Path='AncestryMixing.lean'; Module='AncestryMixing'},
  @{Path='AncestryExamples.lean'; Module='AncestryExamples'},
  @{Path='FeedbackDynamics.lean'; Module='FeedbackDynamics'},
  @{Path='FogartyAffinity.lean'; Module='FogartyAffinity'},
  @{Path='FogartyAffinityFixation.lean'; Module='FogartyAffinityFixation'}
)
$results=@()
$allowed=@('propext','Classical.choice','Quot.sound')
Push-Location $packageRoot
try {
 foreach ($module in $modules) {
  $sourcePath=Join-Path $packageRoot $module.Path
  if (-not (Test-Path -LiteralPath $sourcePath)) { throw ('Missing source: '+$module.Path) }
  $text=[IO.File]::ReadAllText($sourcePath)
  if ($text -match '(?m)^\s*(axiom|constant)\s') { throw ('Unreviewed axiom declaration in '+$module.Path) }
  $outputPath=Join-Path $buildRoot ($module.Module+'.olean')
  New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($outputPath)) | Out-Null
  $logPath=Join-Path $logRoot (($module.Module -replace '/','-')+'.log')
  $moduleRoot=$packageRoot
  if ($module.Path.StartsWith('vendor/')) { $moduleRoot=Join-Path $packageRoot 'vendor' }
  $compilerOutput=(& $LeanExe -j1 -M4096 "--root=$moduleRoot" -o $outputPath $sourcePath 2>&1 | Out-String)
  $compilerExit=$LASTEXITCODE
  [IO.File]::WriteAllText($logPath,$compilerOutput)
  if ($compilerExit -ne 0) { throw ('Lean failed: '+$module.Path+'; see '+$logPath) }
  if ($compilerOutput -match 'sorryAx') { throw ('Admitted proof in '+$module.Path) }
  $audits=[regex]::Matches($compilerOutput,"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
  $emptyAudits=[regex]::Matches($compilerOutput,"'([^']+)' does not depend on any axioms")
  $expectedCount=[regex]::Matches($text,'(?m)^\s*#print axioms\s+').Count
  if ($audits.Count+$emptyAudits.Count -ne $expectedCount) { throw ('Axiom output count mismatch for '+$module.Path) }
  $checked=@()
  foreach ($audit in $audits) {
    $used=@($audit.Groups[2].Value -split ',' | ForEach-Object {$_.Trim()} | Where-Object {$_})
    foreach ($axiomName in $used) {
      if ($allowed -notcontains $axiomName) { throw ('Unexpected axiom: '+$axiomName) }
    }
    $checked += @{declaration=$audit.Groups[1].Value;axioms=$used}
  }
  foreach ($audit in $emptyAudits) { $checked += @{declaration=$audit.Groups[1].Value;axioms=@()} }
  $results += @{path=$module.Path;sha256=(Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash;exitCode=$compilerExit;selectedEndpoints=$checked}
  Write-Output ($module.Path+': PASS; '+$expectedCount+' selected axiom reports')
 }
 $receipt=@{
  timestampUtc=[DateTime]::UtcNow.ToString('o');
  status='PASS';
  lean=$leanVersion;
  mathlibRevision=$actualMathlib;
  mode='Fresh compilation of all packaged custom source against pinned existing Mathlib compiled libraries';
  cleanMachineDownloadTested=$false;
  maximumWorkers=1;
  memoryLimitMb=4096;
  modules=$results
 }
 $receipt | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath (Join-Path $logRoot 'receipt.json') -Encoding utf8
} finally { Pop-Location; $env:LEAN_PATH=$previousLeanPath }
