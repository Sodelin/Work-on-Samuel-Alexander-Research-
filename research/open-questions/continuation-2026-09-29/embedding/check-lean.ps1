param([string]$Source = 'TerminalCloneAvoiders.lean')
$ErrorActionPreference = 'Stop'
$auditDir = $PSScriptRoot
$auditCache = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization'
$auditCompiler = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'
$auditImports = @($auditDir, ($auditCache+'\.lake\build\lib\lean'), ($auditCache+'\real\.lake\build\lib\lean'))
$auditImports += Get-ChildItem -LiteralPath ($auditCache+'\real\.lake\packages') -Directory | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' } | Where-Object { Test-Path -LiteralPath $_ }
$env:LEAN_PATH = $auditImports -join ';'
$auditStem = [System.IO.Path]::GetFileNameWithoutExtension($Source)
$auditLog = Join-Path $auditDir ($auditStem+'.compile.log')
& $auditCompiler --version | Set-Content -LiteralPath $auditLog -Encoding utf8
& $auditCompiler -o (Join-Path $auditDir ($auditStem+'.olean')) (Join-Path $auditDir $Source) 2>&1 | Tee-Object -FilePath $auditLog -Append
$auditExit = $LASTEXITCODE
[ordered]@{source=(Join-Path $auditDir $Source);sha256=(Get-FileHash -LiteralPath (Join-Path $auditDir $Source) -Algorithm SHA256).Hash;compiler=$auditCompiler;exitCode=$auditExit;checkedAt=(Get-Date).ToUniversalTime().ToString('o');imports=$auditImports;log=$auditLog} | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $auditDir ($auditStem+'.check.json')) -Encoding utf8
exit $auditExit
