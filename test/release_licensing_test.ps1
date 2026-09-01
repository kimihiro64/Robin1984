$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$testRoot = Join-Path ([IO.Path]::GetTempPath()) (
  'robin1984-release-licensing-' + [Guid]::NewGuid().ToString('N')
)
$documentationRoot = Join-Path $testRoot 'documentation'
$buildRoot = Join-Path $testRoot 'build'
New-Item -ItemType Directory -Path $documentationRoot -Force | Out-Null
New-Item -ItemType Directory -Path $buildRoot -Force | Out-Null

$documentationTargets = @(
  'index.html',
  'favicon.svg',
  'Robin1984.html',
  'Robin1984/Equivalence/Theorem.html',
  'Robin1984/ColossallyAbundant/CAProfile.html',
  'Robin1984/NicolasLandau/NicolasLandau.html',
  'Robin1984/Finite/FiniteComplete.html',
  'references.html',
  'tactics.html'
)
$template = Join-Path $repositoryRoot 'assets/api-documentation-index.html'
foreach ($relativePath in $documentationTargets) {
  $target = Join-Path $documentationRoot $relativePath
  $parent = Split-Path -Parent $target
  if (-not (Test-Path -LiteralPath $parent)) {
    New-Item -ItemType Directory -Path $parent -Force | Out-Null
  }
  Copy-Item -LiteralPath $template -Destination $target
}

$prepareDocumentation = Join-Path $repositoryRoot 'scripts/prepare-api-docs.ps1'
& $prepareDocumentation -DocumentationRoot $documentationRoot

$licensingRoot = Join-Path $documentationRoot 'licensing'
$licensingIndex = Join-Path $licensingRoot 'index.html'
foreach ($required in @(
  (Join-Path $documentationRoot 'index.html'),
  $licensingIndex,
  (Join-Path $licensingRoot 'Robin1984-Apache-2.0.txt'),
  (Join-Path $licensingRoot 'Robin1984-LICENSING.md')
)) {
  if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
    throw "Prepared documentation is missing '$required'."
  }
}

$indexText = [IO.File]::ReadAllText($licensingIndex)
$manifestPackages = foreach ($manifestPath in @(
  (Join-Path $repositoryRoot 'lake-manifest.json'),
  (Join-Path $repositoryRoot 'docbuild/lake-manifest.json')
)) {
  (Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json).packages |
    Where-Object { $_.type -eq 'git' }
}
foreach ($package in $manifestPackages) {
  if (-not $indexText.Contains([Net.WebUtility]::HtmlEncode([string]$package.url))) {
    throw "Licensing index omits dependency '$($package.url)'."
  }
}
if (-not $indexText.Contains('Lean 4 toolchain')) {
  throw 'Licensing index omits the Lean 4 toolchain.'
}

$links = [regex]::Matches($indexText, 'href="\.\/([^"]+)"')
foreach ($link in $links) {
  $target = Join-Path $licensingRoot $link.Groups[1].Value
  if (-not (Test-Path -LiteralPath $target)) {
    throw "Licensing index has a broken relative link '$($link.Groups[1].Value)'."
  }
}

$preparedHash = (Get-FileHash -LiteralPath $licensingIndex -Algorithm SHA256).Hash
& $prepareDocumentation `
  -DocumentationRoot $documentationRoot `
  -UsePreparedLicensing
$consumerHash = (Get-FileHash -LiteralPath $licensingIndex -Algorithm SHA256).Hash
if ($consumerHash -cne $preparedHash) {
  throw 'Release-consumer validation rewrote the prepared licensing bundle.'
}

& (Join-Path $repositoryRoot 'scripts/prepare-release-licensing.ps1') `
  -DestinationRoot $buildRoot
foreach ($required in @(
  (Join-Path $buildRoot 'licensing/index.html'),
  (Join-Path $buildRoot 'licensing/Robin1984-Apache-2.0.txt'),
  (Join-Path $buildRoot 'licensing/Robin1984-LICENSING.md')
)) {
  if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
    throw "Prepared build archive is missing '$required'."
  }
}

Write-Host "Release licensing smoke test passed for $($manifestPackages.Count) manifest package entries."
