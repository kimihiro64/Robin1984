param(
  [string]$RepositoryRoot = (Split-Path -Parent $PSScriptRoot)
)

$ErrorActionPreference = 'Stop'
$taskRoot = [IO.Path]::GetFullPath($RepositoryRoot)
$taskLedgerPath = Join-Path $taskRoot 'provenance\ledger.json'
if (-not (Test-Path -LiteralPath $taskLedgerPath -PathType Leaf)) {
  throw 'The reviewed provenance ledger does not exist yet.'
}
$taskLedger = Get-Content -LiteralPath $taskLedgerPath -Raw | ConvertFrom-Json
if (@($taskLedger.files).Count -eq 0) {
  throw 'The reviewed provenance ledger contains no file entries.'
}
$taskUnreviewed = @($taskLedger.files | Where-Object { $_.reviewed -ne $true })
if ($taskUnreviewed.Count -ne 0) {
  throw "The provenance ledger has $($taskUnreviewed.Count) unreviewed entries."
}
$taskFiles = Get-ChildItem -LiteralPath $taskRoot -Recurse -File -Filter '*.lean' |
  Where-Object {
    $_.FullName -notmatch '[\\/]\.lake[\\/]'
  }

$taskFailures = [Collections.Generic.List[string]]::new()
$taskLedgerByPath = @{}
foreach ($taskEntry in @($taskLedger.files)) {
  $taskPath = [string]$taskEntry.path
  if ([string]::IsNullOrWhiteSpace($taskPath)) {
    $taskFailures.Add('Ledger entry with empty path')
    continue
  }
  if ($taskLedgerByPath.ContainsKey($taskPath)) {
    $taskFailures.Add("Duplicate ledger path: $taskPath")
    continue
  }
  if ([string]::IsNullOrWhiteSpace([string]$taskEntry.content_basis)) {
    $taskFailures.Add("Missing content review evidence: $taskPath")
  }
  if ([string]::IsNullOrWhiteSpace([string]$taskEntry.dependency_status)) {
    $taskFailures.Add("Missing dependency status: $taskPath")
  }
  $taskLedgerByPath[$taskPath] = $taskEntry
}

$taskSourcePaths = [Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal
)
foreach ($taskFile in $taskFiles) {
  $taskRelative = [IO.Path]::GetRelativePath($taskRoot, $taskFile.FullName).Replace(
    [IO.Path]::DirectorySeparatorChar,
    '/'
  )
  [void]$taskSourcePaths.Add($taskRelative)
  if (-not $taskLedgerByPath.ContainsKey($taskRelative)) {
    $taskFailures.Add("Source file missing from ledger: $taskRelative")
  }
}
foreach ($taskPath in $taskLedgerByPath.Keys) {
  if (-not $taskSourcePaths.Contains($taskPath)) {
    $taskFailures.Add("Ledger path has no source file: $taskPath")
  }
}

foreach ($taskFile in $taskFiles) {
  $taskRelative = [IO.Path]::GetRelativePath($taskRoot, $taskFile.FullName).Replace(
    [IO.Path]::DirectorySeparatorChar,
    '/'
  )
  $taskIsMathlibCandidate = $taskRelative.StartsWith(
    'Robin1984/Mathlib/',
    [StringComparison]::Ordinal
  )
  $taskText = [IO.File]::ReadAllText($taskFile.FullName)
  $taskModuleDocs = [Text.RegularExpressions.Regex]::Matches(
    $taskText,
    '(?s)/-!(.*?)-/'
  )
  $taskSubstantiveModuleDocs = @($taskModuleDocs | Where-Object {
    $taskBody = $_.Groups[1].Value.Trim()
    -not $taskBody.Contains('## Provenance') -and
      -not [string]::IsNullOrWhiteSpace($taskBody)
  })
  if ($taskIsMathlibCandidate) {
    foreach ($taskMarker in @(
        'Copyright (c)',
        'Released under Apache 2.0 license',
        'Authors:'
      )) {
      if (-not $taskText.Contains($taskMarker)) {
        $taskFailures.Add("Missing Mathlib source marker '$taskMarker': $taskRelative")
      }
    }
    if ($taskSubstantiveModuleDocs.Count -lt 1) {
      $taskFailures.Add("Missing substantive module documentation: $taskRelative")
    }
    continue
  }
  $taskCount = [Text.RegularExpressions.Regex]::Matches(
    $taskText,
    '(?m)^## Provenance$'
  ).Count
  $taskClassCount = [Text.RegularExpressions.Regex]::Matches(
    $taskText,
    '(?m)^- Classification: \*\*(Direct source formalization|Other published source formalization|Standard mathematical formalization|Primarily project-original)\*\*\.$'
  ).Count
  $taskSourceCount = [Text.RegularExpressions.Regex]::Matches(
    $taskText,
    '(?m)^- Mathematical source: .+$'
  ).Count
  $taskNoteCount = [Text.RegularExpressions.Regex]::Matches(
    $taskText,
    '(?m)^- Formalization note: .+$'
  ).Count
  if ($taskCount -ne 1 -or $taskClassCount -ne 1 -or $taskSourceCount -ne 1 -or $taskNoteCount -ne 1) {
    $taskFailures.Add("Missing or malformed provenance header: $taskRelative")
    continue
  }
  if ($taskSubstantiveModuleDocs.Count -lt 1) {
    $taskFailures.Add("Missing substantive module documentation: $taskRelative")
  }
  if ($taskLedgerByPath.ContainsKey($taskRelative)) {
    $taskEntry = $taskLedgerByPath[$taskRelative]
    $taskExpectedClass = "- Classification: **$($taskEntry.classification)**."
    $taskExpectedSource = "- Mathematical source: $($taskEntry.mathematical_source)"
    $taskExpectedNote = "- Formalization note: $($taskEntry.formalization_note)"
    if (-not $taskText.Contains($taskExpectedClass)) {
      $taskFailures.Add("Header/ledger classification mismatch: $taskRelative")
    }
    if (-not $taskText.Contains($taskExpectedSource)) {
      $taskFailures.Add("Header/ledger source mismatch: $taskRelative")
    }
    if (-not $taskText.Contains($taskExpectedNote)) {
      $taskFailures.Add("Header/ledger note mismatch: $taskRelative")
    }
  }
}

if ($taskFailures.Count -ne 0) {
  $taskFailures | ForEach-Object { Write-Error $_ }
  exit 1
}

Write-Output "Validated exact reviewed provenance for $($taskFiles.Count) Lean files."
