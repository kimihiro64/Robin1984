$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$lakeCommand = Get-Command lake -ErrorAction Stop
$ripgrepCommand = Get-Command rg -ErrorAction Stop

& (Join-Path $PSScriptRoot 'bootstrap.ps1')
if (-not $?) {
  throw 'bootstrap failed'
}

& (Join-Path $PSScriptRoot 'check-provenance.ps1') -RepositoryRoot $repositoryRoot
if (-not $?) {
  throw 'provenance validation failed'
}

& (Join-Path $PSScriptRoot 'check-imports.ps1') -RepositoryRoot $repositoryRoot
if (-not $?) {
  throw 'import lint failed'
}

Push-Location $repositoryRoot
try {
  & $lakeCommand.Source build
  if ($LASTEXITCODE -ne 0) {
    throw "lake build failed with exit code $LASTEXITCODE"
  }

  $namespaceArguments = @(
    '-n',
    '-e', '^\s*open\s+Robin\s*$',
    '-e', '^\s*namespace\s+Robin\s*$',
    '-e', '^\s*end\s+Robin\s*$',
    '-g', '*.lean',
    '-g', '!.lake/**',
    $repositoryRoot
  )
  & $ripgrepCommand.Source @namespaceArguments
  if ($LASTEXITCODE -eq 0) {
    throw 'A bare source-repository namespace command remains in Lean code.'
  }
  if ($LASTEXITCODE -ne 1) {
    throw "namespace scan failed with exit code $LASTEXITCODE"
  }
} finally {
  Pop-Location
}
