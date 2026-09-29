param(
    [switch]$Run,
    [string]$Python = 'python',
    [string]$Lean = 'lean'
)
$ErrorActionPreference = 'Stop'
$packetRoot = $PSScriptRoot
function PacketHash([string]$Path) {
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

& $Python (Join-Path $packetRoot 'verify_packet.py')
if ($LASTEXITCODE -ne 0) { throw 'Packet integrity or saved evidence check failed.' }
if (-not $Run) {
    Write-Output 'Integrity only; Lean was not invoked. Pass -Run for a fresh sequential replay.'
    return
}

$dependencyInfo = Get-Content -LiteralPath (Join-Path $packetRoot 'DEPENDENCIES.json') -Raw | ConvertFrom-Json
$priorLeanPath = $env:LEAN_PATH
Push-Location -LiteralPath $packetRoot
try {
    $versionText = (& $Lean --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $versionText -notmatch '4\.33\.1(?![0-9])') {
        throw "Expected Lean 4.33.1; got $versionText"
    }
    $runId = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffZ') + '-' + [Guid]::NewGuid().ToString('N').Substring(0,8)
    $replayDir = Join-Path $packetRoot ('.replay/' + $runId)
    $buildDir = Join-Path $replayDir 'build'
    $logDir = Join-Path $replayDir 'logs'
    $paths = @($buildDir)
    foreach ($dep in $dependencyInfo.packages) {
        $packageDir = Join-Path $packetRoot ('.lake/packages/' + $dep.name)
        if (-not (Test-Path -LiteralPath $packageDir -PathType Container)) {
            throw "Missing pinned dependency $($dep.name). Follow REPRODUCTION.md first."
        }
        $head = (& git -C $packageDir rev-parse HEAD | Out-String).Trim()
        if ($LASTEXITCODE -ne 0 -or $head -ne $dep.rev) { throw "Revision mismatch for $($dep.name)." }
        $libDir = Join-Path $packageDir '.lake/build/lib/lean'
        if (Test-Path -LiteralPath $libDir -PathType Container) { $paths += $libDir }
    }
    $finCases = Join-Path $packetRoot '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/FinCases.olean'
    if (-not (Test-Path -LiteralPath $finCases -PathType Leaf)) { throw 'Mathlib cache missing; follow REPRODUCTION.md.' }
    New-Item -ItemType Directory -Path $buildDir,$logDir -Force | Out-Null
    $env:LEAN_PATH = $paths -join [IO.Path]::PathSeparator
    $worker = Get-Content -LiteralPath (Join-Path $packetRoot 'verification/worker-receipt.json') -Raw | ConvertFrom-Json
    $inherited = Get-Content -LiteralPath (Join-Path $packetRoot 'verification/finite-dependency-receipt.json') -Raw | ConvertFrom-Json
    $allowed = @('propext','Classical.choice','Quot.sound')
    $records = @()
    foreach ($module in @('FiniteFixation','FiniteEpigenetic','PureInductionJoint')) {
        $sourceFile = Join-Path $packetRoot ($module + '.lean')
        $sourceBefore = PacketHash $sourceFile
        $objectFile = Join-Path $buildDir ($module + '.olean')
        $logFile = Join-Path $logDir ($module + '.log')
        & $Lean -j1 -M4096 -o $objectFile $sourceFile 2>&1 | Tee-Object -FilePath $logFile
        $compilerExit = $LASTEXITCODE
        if ($compilerExit -ne 0) { throw "$module failed with exit $compilerExit; see $logFile" }
        if ((PacketHash $sourceFile) -ne $sourceBefore) { throw "$module source changed during compilation." }
        $text = Get-Content -LiteralPath $logFile -Raw
        if ($text -match '\bsorryAx\b|\bnative_decide\b') { throw 'Unexpected proof marker in replay log.' }
        $reports = [regex]::Matches($text, "'([^']+)' depends on axioms:\s*\[([^]]*)\]")
        $names = @($reports | ForEach-Object { $_.Groups[1].Value })
        $expected = if ($module -eq 'PureInductionJoint') { @($worker.selectedEndpoints) } else {
            @(@($inherited.modules | Where-Object module -eq $module)[0].selectedEndpoints)
        }
        if ($names.Count -ne $expected.Count -or (Compare-Object $names $expected)) { throw "Selected endpoint mismatch for $module." }
        foreach ($report in $reports) {
            $axes = @($report.Groups[2].Value.Split(',') | ForEach-Object { $_.Trim() } | Where-Object { $_ })
            foreach ($axis in $axes) { if ($axis -notin $allowed) { throw "Unexpected axiom $axis." } }
        }
        $records += [ordered]@{module=$module;compilerExitCode=$compilerExit;sourceSha256=$sourceBefore;oleanSha256=(PacketHash $objectFile);logSha256=(PacketHash $logFile);selectedEndpoints=$names}
    }
    & $Python (Join-Path $packetRoot 'verify_packet.py')
    if ($LASTEXITCODE -ne 0) { throw 'Original packet integrity changed during replay.' }
    $runReceipt = [ordered]@{status='FRESH_SEQUENTIAL_REPLAY_PASS';leanVersion=$versionText;command='lean -j1 -M4096 -o <replay-object> <source>';records=$records;originalEvidencePreserved=$true}
    $runReceipt | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $replayDir 'RUN-RECEIPT.json') -Encoding utf8
    Write-Output "Replay passed. New evidence: $replayDir"
}
finally {
    $env:LEAN_PATH = $priorLeanPath
    Pop-Location
}
