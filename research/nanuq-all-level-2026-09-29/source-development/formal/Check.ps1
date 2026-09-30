param([string]$File = 'NanuqPositiveCombination.lean')
$ErrorActionPreference = 'Stop'
$taskSourceRoot = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization'
$taskLeanPaths = @($PSScriptRoot, (Join-Path $taskSourceRoot '.lake\build\lib\lean'), (Join-Path $taskSourceRoot 'real\.lake\build\lib\lean'))
foreach ($taskPackage in Get-ChildItem -LiteralPath (Join-Path $taskSourceRoot 'real\.lake\packages') -Directory) {
  $taskLibrary = Join-Path $taskPackage.FullName '.lake\build\lib\lean'
  if (Test-Path -LiteralPath $taskLibrary) { $taskLeanPaths += $taskLibrary }
}
$env:LEAN_PATH = $taskLeanPaths -join ';'
$taskCompiler = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'
$taskName = [IO.Path]::GetFileNameWithoutExtension($File)
Push-Location $PSScriptRoot
try {
  & $taskCompiler -o (Join-Path $PSScriptRoot ($taskName + '.olean')) (Join-Path $PSScriptRoot $File) 2>&1 | Tee-Object -FilePath (Join-Path $PSScriptRoot ($taskName + '.log'))
  $taskResult = $LASTEXITCODE
} finally {
  Pop-Location
}
exit $taskResult
