$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$lakeCommand = Get-Command lake -ErrorAction Stop

Push-Location $repositoryRoot
try {
  & $lakeCommand.Source update
  if ($LASTEXITCODE -ne 0) {
    throw "lake update failed with exit code $LASTEXITCODE"
  }
} finally {
  Pop-Location
}
