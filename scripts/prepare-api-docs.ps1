param(
  [Parameter(Mandatory = $true)]
  [string]$DocumentationRoot,

  [string]$TemplatePath =
    (Join-Path $PSScriptRoot '../assets/api-documentation-index.html'),

  [switch]$UsePreparedLicensing
)

$ErrorActionPreference = 'Stop'

$root = (Resolve-Path -LiteralPath $DocumentationRoot).Path
$template = (Resolve-Path -LiteralPath $TemplatePath).Path
$index = Join-Path $root 'index.html'
if (-not (Test-Path -LiteralPath $index -PathType Leaf)) {
  throw "Generated documentation has no index.html: $index"
}

if (-not $UsePreparedLicensing) {
  & (Join-Path $PSScriptRoot 'prepare-release-licensing.ps1') `
    -DestinationRoot $root `
    -IncludeDependencyLicenses
}

$templateText = [IO.File]::ReadAllText($template)
foreach ($forbidden in @('<script', '<iframe', 'http://', 'https://')) {
  if ($templateText.Contains($forbidden, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Offline documentation template contains forbidden text '$forbidden'."
  }
}

$hrefs = @(
  [regex]::Matches($templateText, 'href="([^"]+)"') |
    ForEach-Object { $_.Groups[1].Value }
)
if ($hrefs.Count -eq 0) {
  throw 'Offline documentation template contains no links.'
}

$rootPrefix = $root.TrimEnd(
  [IO.Path]::DirectorySeparatorChar,
  [IO.Path]::AltDirectorySeparatorChar
) + [IO.Path]::DirectorySeparatorChar
foreach ($href in $hrefs) {
  if (-not $href.StartsWith('./', [StringComparison]::Ordinal)) {
    throw "Offline documentation link is not relative: $href"
  }
  $relative = $href.Substring(2).Replace(
    [IO.Path]::AltDirectorySeparatorChar,
    [IO.Path]::DirectorySeparatorChar
  )
  $target = [IO.Path]::GetFullPath((Join-Path $root $relative))
  if (-not $target.StartsWith($rootPrefix, [StringComparison]::Ordinal)) {
    throw "Offline documentation link escapes the documentation root: $href"
  }
  if (-not (Test-Path -LiteralPath $target -PathType Leaf)) {
    throw "Offline documentation link target is missing: $href"
  }
}

Copy-Item -LiteralPath $template -Destination $index -Force
$templateHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $template).Hash
$indexHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $index).Hash
if ($templateHash -cne $indexHash) {
  throw 'Prepared documentation index does not match its committed template.'
}

Write-Host "Prepared offline API documentation index with $($hrefs.Count) verified links."
