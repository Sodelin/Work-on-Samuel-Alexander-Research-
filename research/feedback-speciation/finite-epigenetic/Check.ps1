[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)]
  [ValidateSet('FiniteFixation.lean','FiniteEpigenetic.lean','DeterministicEpigenetic.lean','RankingReversal.lean')]
  [string]$File,
  [string]$PackagesPath = (Join-Path $PSScriptRoot '.lake\packages'),
  [string]$LeanCommand = 'lean',
  [string]$OutputDirectory = (Join-Path $PSScriptRoot 'replay')
)
$ErrorActionPreference='Stop'
$finiteRoot=$PSScriptRoot
$finitePackages=[IO.Path]::GetFullPath($PackagesPath)
$finiteOutput=[IO.Path]::GetFullPath($OutputDirectory)
$finiteBuild=Join-Path $finiteOutput 'build'
$finiteLogs=Join-Path $finiteOutput 'logs'
New-Item -ItemType Directory -Force -Path $finiteBuild,$finiteLogs | Out-Null
if(-not (Test-Path -LiteralPath $finitePackages -PathType Container)) {
  throw "PackagesPath is not a directory: $finitePackages. Run lake build first or pass -PackagesPath."
}
$finitePaths=@($finiteBuild)
foreach($finitePackage in Get-ChildItem -LiteralPath $finitePackages -Directory) {
  $finiteLib=Join-Path $finitePackage.FullName '.lake\build\lib\lean'
  if(Test-Path -LiteralPath $finiteLib -PathType Container){$finitePaths+=$finiteLib}
}
$env:LEAN_PATH=$finitePaths -join ';'
$finiteStem=[IO.Path]::GetFileNameWithoutExtension($File)
$finiteSource=Join-Path $finiteRoot $File
if(-not (Test-Path -LiteralPath $finiteSource -PathType Leaf)){throw "Lean source not found: $finiteSource"}
$finiteLog=Join-Path $finiteLogs ($finiteStem+'.log')
$finiteOlean=Join-Path $finiteBuild ($finiteStem+'.olean')
& $LeanCommand -j1 -M4096 -o $finiteOlean $finiteSource *> $finiteLog
$finiteExit=$LASTEXITCODE
Get-Content -LiteralPath $finiteLog
exit $finiteExit
