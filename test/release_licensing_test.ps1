$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$buildRoot = Join-Path ([IO.Path]::GetTempPath()) (
  'robin1984-release-licensing-' + [Guid]::NewGuid().ToString('N')
)
New-Item -ItemType Directory -Path $buildRoot | Out-Null

& (Join-Path $repositoryRoot 'scripts/prepare-release-licensing.ps1') `
  -DestinationRoot $buildRoot

$licensingRoot = Join-Path $buildRoot 'licensing'
$licensingIndex = Join-Path $licensingRoot 'index.html'
foreach ($required in @(
  $licensingIndex,
  (Join-Path $licensingRoot 'Robin1984-Apache-2.0.txt'),
  (Join-Path $licensingRoot 'Robin1984-LICENSING.md')
)) {
  if (-not (Test-Path -LiteralPath $required -PathType Leaf)) {
    throw "Prepared build archive is missing '$required'."
  }
}

$indexText = [IO.File]::ReadAllText($licensingIndex)
$links = [regex]::Matches($indexText, 'href="\./([^"]+)"')
if ($links.Count -eq 0) {
  throw 'The release licensing index contains no relative licence links.'
}
foreach ($link in $links) {
  $target = Join-Path $licensingRoot $link.Groups[1].Value
  if (-not (Test-Path -LiteralPath $target -PathType Leaf)) {
    throw "Licensing index has a broken relative link '$($link.Groups[1].Value)'."
  }
}

Write-Host 'Lean-build archive licensing smoke test passed.'
