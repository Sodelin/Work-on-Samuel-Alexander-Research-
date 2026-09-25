param([switch]$Run,[string]$Python='python',[string]$Lean='lean',[string]$MathlibPackages='')
$ErrorActionPreference='Stop'
$packetRoot=$PSScriptRoot
& $Python (Join-Path $packetRoot 'verify_packet.py')
if($LASTEXITCODE -ne 0){throw 'Packet integrity check failed.'}
if(-not $Run){Write-Output 'Integrity only; no Lean process started.'; return}
if(-not $MathlibPackages){$MathlibPackages=Join-Path $packetRoot '.lake/packages'}
$dep=Get-Content -Raw -LiteralPath (Join-Path $packetRoot 'DEPENDENCIES.json')|ConvertFrom-Json
$version=(& $Lean --version|Out-String).Trim()
if($LASTEXITCODE -ne 0 -or $version -notmatch 'version 4\.33\.1\b'){throw 'Lean 4.33.1 required.'}
foreach($p in $dep.packages){
 $pdir=Join-Path $MathlibPackages $p.name
 $head=(& git -c "safe.directory=$($pdir -replace '\\','/')" -C $pdir rev-parse HEAD|Out-String).Trim()
 if($LASTEXITCODE -ne 0 -or $head -ne $p.rev){throw "Dependency revision mismatch: $($p.name)"}
}
$runId=[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffZ')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8)
$outRoot=Join-Path $packetRoot ('.replay/'+$runId)
$build=Join-Path $outRoot 'build'
$logs=Join-Path $outRoot 'logs'
New-Item -ItemType Directory -Force -Path $build,$logs|Out-Null
$paths=@($build)
foreach($p in $dep.packages){
 $lib=Join-Path (Join-Path $MathlibPackages $p.name) '.lake/build/lib/lean'
 if(Test-Path -LiteralPath $lib -PathType Container){$paths+=$lib}
}
function ProofHash([string]$file){(Get-FileHash -Algorithm SHA256 -LiteralPath $file).Hash.ToLowerInvariant()}
$priorPath=$env:LEAN_PATH
$env:LEAN_PATH=$paths -join [IO.Path]::PathSeparator
$records=@()
try{
 foreach($module in $dep.localSourceOrder){
  $relative=$module.Replace('.','/')+'.lean'
  $source=Join-Path $packetRoot $relative
  $sourceBefore=ProofHash $source
  $text=[IO.File]::ReadAllText($source)
  if($text -match '(?m)^\s*(axiom|constant)\s|\bsorry\b|\badmit\b|\bnative_decide\b'){throw "Unreviewed source marker: $module"}
  $object=Join-Path $build ($module.Replace('.','/')+'.olean')
  New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($object))|Out-Null
  $log=Join-Path $logs ($module+'.log')
  $output=(& $Lean -j1 -M4096 "--root=$packetRoot" -o $object $source 2>&1|Out-String)
  $code=$LASTEXITCODE
  [IO.File]::WriteAllText($log,$output,[Text.UTF8Encoding]::new($false))
  if($code -ne 0){throw "Lean failed on $module; inspect $log"}
  if((ProofHash $source) -ne $sourceBefore){throw "Source changed during replay: $module"}
  $reports=[regex]::Matches($output,"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
  $empty=[regex]::Matches($output,"'([^']+)' does not depend on any axioms")
  $expected=@([regex]::Matches($text,'(?m)^\s*#print axioms\s+(\S+)')|ForEach-Object {$_.Groups[1].Value})
  if($reports.Count+$empty.Count -ne $expected.Count){throw "Axiom report count mismatch: $module"}
  $names=@()
  foreach($r in $reports){
   $names+=$r.Groups[1].Value
   foreach($a in ($r.Groups[2].Value -split ',')){
    if(@('propext','Classical.choice','Quot.sound') -notcontains $a.Trim()){throw "Unexpected axiom: $a"}
   }
  }
  foreach($r in $empty){$names+=$r.Groups[1].Value}
  foreach($name in $expected){
   $matching=@($names|Where-Object {$_ -eq $name -or $_.EndsWith('.'+$name)})
   if($matching.Count -ne 1){throw "Missing or ambiguous axiom report: $name"}
  }
  $records+=@{module=$module;sourceSha256=$sourceBefore;oleanSha256=(ProofHash $object);logSha256=(ProofHash $log);compilerExitCode=$code;selectedEndpoints=$names}
  Write-Output "${module}: PASS"
 }
 & $Python (Join-Path $packetRoot 'verify_packet.py')
 if($LASTEXITCODE -ne 0){throw 'Original packet changed during replay.'}
 $receipt=@{status='FRESH_SEQUENTIAL_REPLAY_PASS';leanVersion=$version;maximumWorkers=1;memoryLimitMb=4096;records=$records}
 [IO.File]::WriteAllText((Join-Path $outRoot 'RUN-RECEIPT.json'),($receipt|ConvertTo-Json -Depth 10),[Text.UTF8Encoding]::new($false))
}finally{$env:LEAN_PATH=$priorPath}
