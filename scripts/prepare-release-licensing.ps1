param(
  [Parameter(Mandatory = $true)]
  [string]$DestinationRoot,

  [switch]$IncludeDependencyLicenses
)

$ErrorActionPreference = 'Stop'

$repositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$destination = (Resolve-Path -LiteralPath $DestinationRoot).Path
$destinationPrefix = $destination.TrimEnd(
  [IO.Path]::DirectorySeparatorChar,
  [IO.Path]::AltDirectorySeparatorChar
) + [IO.Path]::DirectorySeparatorChar
$licensingRoot = Join-Path $destination 'licensing'
$licensingFullPath = [IO.Path]::GetFullPath($licensingRoot)
if (-not $licensingFullPath.StartsWith($destinationPrefix, [StringComparison]::OrdinalIgnoreCase)) {
  throw "Licensing output escapes the requested destination: $licensingFullPath"
}

if (Test-Path -LiteralPath $licensingFullPath) {
  $resolvedExisting = (Resolve-Path -LiteralPath $licensingFullPath).Path
  if (-not $resolvedExisting.StartsWith($destinationPrefix, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Refusing to replace licensing output outside the requested destination: $resolvedExisting"
  }
  Remove-Item -LiteralPath $resolvedExisting -Recurse -Force
}
New-Item -ItemType Directory -Path $licensingFullPath | Out-Null

Copy-Item -LiteralPath (Join-Path $repositoryRoot 'LICENSE') `
  -Destination (Join-Path $licensingFullPath 'Robin1984-Apache-2.0.txt')
Copy-Item -LiteralPath (Join-Path $repositoryRoot 'LICENSING.md') `
  -Destination (Join-Path $licensingFullPath 'Robin1984-LICENSING.md')

$entries = [Collections.Generic.List[object]]::new()
$entries.Add([PSCustomObject]@{
  Name = 'Robin1984'
  Source = 'This repository'
  Revision = 'Release commit'
  Files = @('Robin1984-Apache-2.0.txt', 'Robin1984-LICENSING.md')
})

if ($IncludeDependencyLicenses) {
  $gitCommand = Get-Command git -ErrorAction Stop
  $leanCommand = Get-Command lean -ErrorAction Stop
  $packagesRoot = (Resolve-Path -LiteralPath (Join-Path $repositoryRoot '.lake/packages')).Path

  function Normalize-GitUrl([string]$Url) {
    return ($Url.Trim().TrimEnd('/') -replace '\.git$', '').ToLowerInvariant()
  }

  $packageDirectoriesByUrl = @{}
  foreach ($directory in Get-ChildItem -LiteralPath $packagesRoot -Directory) {
    $remote = (& $gitCommand.Source -C $directory.FullName config --get remote.origin.url 2>$null)
    if ($LASTEXITCODE -eq 0 -and -not [string]::IsNullOrWhiteSpace($remote)) {
      $packageDirectoriesByUrl[(Normalize-GitUrl $remote)] = $directory.FullName
    }
  }

  $packagesByIdentity = [ordered]@{}
  foreach ($manifestPath in @(
    (Join-Path $repositoryRoot 'lake-manifest.json'),
    (Join-Path $repositoryRoot 'docbuild/lake-manifest.json')
  )) {
    $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
    foreach ($package in $manifest.packages | Where-Object { $_.type -eq 'git' }) {
      $identity = "$(Normalize-GitUrl $package.url)@$($package.rev)"
      if (-not $packagesByIdentity.Contains($identity)) {
        $packagesByIdentity[$identity] = $package
      }
    }
  }

  $dependenciesRoot = Join-Path $licensingFullPath 'dependencies'
  New-Item -ItemType Directory -Path $dependenciesRoot | Out-Null
  foreach ($package in $packagesByIdentity.Values) {
    $normalizedUrl = Normalize-GitUrl $package.url
    if (-not $packageDirectoriesByUrl.ContainsKey($normalizedUrl)) {
      throw "Cannot locate the checked-out package for $($package.url). Run lake update first."
    }
    $packageDirectory = $packageDirectoriesByUrl[$normalizedUrl]
    $displayName = [string]$package.name
    $safeName = ($displayName -replace '[^A-Za-z0-9._-]', '')
    if ([string]::IsNullOrWhiteSpace($safeName)) {
      throw "Cannot derive a safe licensing directory for package '$displayName'."
    }
    $packageOutput = Join-Path $dependenciesRoot $safeName
    New-Item -ItemType Directory -Path $packageOutput | Out-Null
    $notices = @(
      Get-ChildItem -LiteralPath $packageDirectory -Force |
        Where-Object { $_.Name -match '^(LICENSE|LICENCE|COPYING|NOTICE)(S)?(?:\.|$)' }
    )
    if ($notices.Count -eq 0) {
      throw "Package '$displayName' has no top-level licence or notice file."
    }
    foreach ($notice in $notices) {
      Copy-Item -LiteralPath $notice.FullName -Destination $packageOutput -Recurse
    }
    $entries.Add([PSCustomObject]@{
      Name = $displayName
      Source = [string]$package.url
      Revision = [string]$package.rev
      Files = @($notices | ForEach-Object { "dependencies/$safeName/$($_.Name)" })
    })
  }

  $leanPrefixText = (& $leanCommand.Source --print-prefix)
  if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($leanPrefixText)) {
    throw 'Unable to resolve the active Lean toolchain prefix.'
  }
  $leanPrefix = (Resolve-Path -LiteralPath $leanPrefixText.Trim()).Path
  $leanOutput = Join-Path $dependenciesRoot 'Lean4'
  New-Item -ItemType Directory -Path $leanOutput | Out-Null
  $leanNotices = @(
    Get-ChildItem -LiteralPath $leanPrefix -Force |
      Where-Object { $_.Name -match '^(LICENSE|LICENCE|COPYING|NOTICE)(S)?(?:\.|$)' }
  )
  if ($leanNotices.Count -eq 0) {
    throw "Lean toolchain at '$leanPrefix' has no top-level licence or notice file."
  }
  foreach ($notice in $leanNotices) {
    Copy-Item -LiteralPath $notice.FullName -Destination $leanOutput -Recurse
  }
  $leanVersion = ((& $leanCommand.Source --version) -join ' ').Trim()
  $entries.Add([PSCustomObject]@{
    Name = 'Lean 4 toolchain'
    Source = $leanVersion
    Revision = 'Selected by lean-toolchain'
    Files = @($leanNotices | ForEach-Object { "dependencies/Lean4/$($_.Name)" })
  })
}

function ConvertTo-HtmlText([string]$Text) {
  return [Net.WebUtility]::HtmlEncode($Text)
}

$rows = foreach ($entry in $entries) {
  $links = foreach ($file in $entry.Files) {
    $encodedFile = ConvertTo-HtmlText ($file -replace '\\', '/')
    '<a href="./{0}">{0}</a>' -f $encodedFile
  }
  '<tr><td>{0}</td><td><code>{1}</code></td><td><code>{2}</code></td><td>{3}</td></tr>' -f `
    (ConvertTo-HtmlText $entry.Name), `
    (ConvertTo-HtmlText $entry.Source), `
    (ConvertTo-HtmlText $entry.Revision), `
    ($links -join '<br>')
}

$document = @"
<!doctype html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Robin1984 licensing</title>
  <style>
    body { max-width: 1100px; margin: 2rem auto; padding: 0 1rem; font: 16px/1.5 system-ui, sans-serif; }
    table { width: 100%; border-collapse: collapse; }
    th, td { border: 1px solid #999; padding: .6rem; text-align: left; vertical-align: top; }
    code { overflow-wrap: anywhere; }
  </style>
</head>
<body>
  <h1>Robin1984 licensing</h1>
  <p>The repository's original material is Apache-2.0 by default. The research paper is also offered under CC-BY-4.0. Mathematical provenance and copyright licensing are separate. See <a href="./Robin1984-LICENSING.md">the complete scope statement</a>.</p>
  <h2>Included notices</h2>
  <table>
    <thead><tr><th>Component</th><th>Source</th><th>Revision</th><th>Licence and notice files</th></tr></thead>
    <tbody>
$($rows -join "`n")
    </tbody>
  </table>
</body>
</html>
"@
[IO.File]::WriteAllText((Join-Path $licensingFullPath 'index.html'), $document)

Write-Host "Prepared licensing information for $($entries.Count) component(s)."
