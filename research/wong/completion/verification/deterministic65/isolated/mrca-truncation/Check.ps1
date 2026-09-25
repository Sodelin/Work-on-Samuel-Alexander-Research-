$ErrorActionPreference = 'Stop'
$owner = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization'
$compiler = 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe'
$cache = Join-Path $PSScriptRoot '.lake\build\lib\lean'
New-Item -ItemType Directory -Path $cache -Force | Out-Null
$paths = @($cache, (Join-Path $owner '.lake\build\lib\lean'), (Join-Path $owner 'real\.lake\build\lib\lean'))
$paths += Get-ChildItem -LiteralPath (Join-Path $owner 'real\.lake\packages') -Directory | ForEach-Object { Join-Path $_.FullName '.lake\build\lib\lean' }
$env:LEAN_PATH = $paths -join ';'
Push-Location $PSScriptRoot
try {
  & $compiler -o (Join-Path $cache 'WongMRCATruncation.olean') 'WongMRCATruncation.lean'
  if ($LASTEXITCODE -ne 0) { throw 'WongMRCATruncation compilation failed' }
} finally { Pop-Location }
