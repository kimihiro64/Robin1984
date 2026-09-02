param(
  [string]$RepositoryRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
)

$ErrorActionPreference = 'Stop'

$sourceRoots = [System.Collections.Generic.List[string]]::new()
$sourceRoots.Add($RepositoryRoot)

$packagesRoot = Join-Path $RepositoryRoot '.lake/packages'
if (Test-Path -LiteralPath $packagesRoot) {
  Get-ChildItem -LiteralPath $packagesRoot -Directory | ForEach-Object {
    $sourceRoots.Add($_.FullName)
  }
}

$directImportCache = @{}
$modulePathCache = @{}
$reachabilityCache = @{}
$failures = [System.Collections.Generic.List[string]]::new()
$mathlibCandidateRoot = 'Robin1984.Mathlib'
$mathlibAllowedExternalPrefixes = @('Batteries.', 'Init.', 'Lean.', 'Mathlib.', 'Std.')
$mathlibHeaderMarkers = @(
  'Copyright (c)',
  'Released under Apache 2.0 license',
  'Authors:',
  '/-!'
)
$mathlibReadinessStates = @(
  'extracting',
  'project-verified',
  'mathlib-ready',
  'submitted',
  'upstreamed'
)
$compatibilityUnfoldPairs = @(
  @('AtTopOmegaMinus', 'Asymptotics.AtTopOmegaMinus'),
  @('AtTopOmegaPlus', 'Asymptotics.AtTopOmegaPlus'),
  @('nicolasMertensProduct', 'Chebyshev.mertensProduct'),
  @('robinLogLower', 'Rat.logSeriesLower'),
  @('robinLogUpper', 'Rat.logSeriesUpper'),
  @('robinTailTriangle', 'MeasureTheory.tailTriangle')
)

function Get-HeaderImportsFromText {
  param(
    [string]$Text,
    [string]$Label
  )

  $imports = [System.Collections.Generic.List[string]]::new()
  $depth = 0
  $stoppedAtBody = $false
  foreach ($rawLine in $Text -split "`r?`n") {
    $builder = [System.Text.StringBuilder]::new($rawLine.Length)
    $index = 0
    while ($index -lt $rawLine.Length) {
      $hasNext = $index + 1 -lt $rawLine.Length
      if ($depth -eq 0 -and $hasNext -and
          $rawLine[$index] -eq '-' -and $rawLine[$index + 1] -eq '-') {
        break
      }
      if ($hasNext -and
          $rawLine[$index] -eq '/' -and $rawLine[$index + 1] -eq '-') {
        $depth += 1
        $index += 2
        continue
      }
      if ($depth -gt 0 -and $hasNext -and
          $rawLine[$index] -eq '-' -and $rawLine[$index + 1] -eq '/') {
        $depth -= 1
        $index += 2
        continue
      }
      if ($depth -eq 0) {
        [void]$builder.Append($rawLine[$index])
      }
      $index += 1
    }

    $line = $builder.ToString()
    if ([string]::IsNullOrWhiteSpace($line)) {
      continue
    }
    if ($line -match '^\s*(?:prelude|module)\s*$') {
      continue
    }
    if ($line -match '^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import(?:\s+all)?\s+([A-Za-z0-9_''.]+)\s*$') {
      $imports.Add($Matches[1])
      continue
    }
    $stoppedAtBody = $true
    break
  }
  if (-not $stoppedAtBody -and $depth -ne 0) {
    throw "$Label has an unterminated Lean block comment in its header"
  }
  return @($imports)
}

function Get-DirectImports {
  param([string]$Path)

  if ($directImportCache.ContainsKey($Path)) {
    return @($directImportCache[$Path])
  }

  $sourceText = [IO.File]::ReadAllText($Path)
  $imports = @(Get-HeaderImportsFromText -Text $sourceText -Label $Path)
  $directImportCache[$Path] = @($imports)
  return @($imports)
}

$parserFixture = @'
/-
import False.From.LeadingComment
/- import False.From.NestedComment -/
-/
module
public import Mathlib.Data.Nat.Basic
/-!
import False.From.ModuleDoc
-/
#check Nat
#eval "/-"
'@
$fixtureImports = @(Get-HeaderImportsFromText -Text $parserFixture -Label 'import parser fixture')
if ($fixtureImports.Count -ne 1 -or $fixtureImports[0] -cne 'Mathlib.Data.Nat.Basic') {
  throw 'Import parser fixture failed.'
}

function Resolve-ModulePath {
  param([string]$Module)

  if ($modulePathCache.ContainsKey($Module)) {
    return $modulePathCache[$Module]
  }

  $relativePath = ($Module -replace '\.', [IO.Path]::DirectorySeparatorChar) + '.lean'
  foreach ($root in $sourceRoots) {
    $candidate = Join-Path $root $relativePath
    if (Test-Path -LiteralPath $candidate -PathType Leaf) {
      $resolved = (Resolve-Path -LiteralPath $candidate).Path
      $modulePathCache[$Module] = $resolved
      return $resolved
    }
  }

  $modulePathCache[$Module] = $null
  return $null
}

function Test-OwnedModuleName {
  param([string]$Module)

  return $Module -ceq 'Challenge' -or
    $Module -ceq 'Solution' -or
    $Module.StartsWith('Robin1984.', [System.StringComparison]::Ordinal)
}

function Get-OwnedImportsInClosure {
  param([string[]]$RootImports)

  $visited = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
  )
  $owned = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
  )
  $pending = [System.Collections.Generic.Stack[string]]::new()
  foreach ($rootImport in $RootImports) {
    $pending.Push($rootImport)
  }

  while ($pending.Count -ne 0) {
    $module = $pending.Pop()
    if (-not $visited.Add($module)) {
      continue
    }
    if (Test-OwnedModuleName -Module $module) {
      [void]$owned.Add($module)
      continue
    }
    $path = Resolve-ModulePath -Module $module
    if ($null -eq $path) {
      continue
    }
    foreach ($import in Get-DirectImports -Path $path) {
      if (-not $visited.Contains($import)) {
        $pending.Push($import)
      }
    }
  }

  return @($owned | Sort-Object -CaseSensitive)
}

function Test-TransitivelyImports {
  param(
    [string]$Provider,
    [string]$Candidate
  )

  $cacheKey = "$Provider`0$Candidate"
  if ($reachabilityCache.ContainsKey($cacheKey)) {
    return [bool]$reachabilityCache[$cacheKey]
  }

  $visited = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
  )
  $pending = [System.Collections.Generic.Stack[string]]::new()
  $pending.Push($Provider)
  while ($pending.Count -ne 0) {
    $module = $pending.Pop()
    if (-not $visited.Add($module)) {
      continue
    }
    $path = Resolve-ModulePath -Module $module
    if ($null -eq $path) {
      continue
    }
    foreach ($import in Get-DirectImports -Path $path) {
      if ($import -ceq $Candidate) {
        $reachabilityCache[$cacheKey] = $true
        return $true
      }
      if ((Test-OwnedModuleName -Module $import) -and
          -not $visited.Contains($import)) {
        $pending.Push($import)
      }
    }
  }

  $reachabilityCache[$cacheKey] = $false
  return $false
}

function Test-BroadImport {
  param([string]$Module)

  if ($Module -in @(
      'Batteries',
      'ImportGraph',
      'LeanCert',
      'Mathlib',
      'PrimeNumberTheoremAnd',
      'Robin1984'
    )) {
    return $true
  }

  return $Module -match '^Mathlib\.(Algebra|Analysis|CategoryTheory|Combinatorics|Data|Geometry|LinearAlgebra|Logic|MeasureTheory|NumberTheory|Order|Probability|SetTheory|Tactic|Topology)$'
}

$ownedFiles = [System.Collections.Generic.List[System.IO.FileInfo]]::new()
foreach ($rootFile in @('Challenge.lean', 'Solution.lean')) {
  $path = Join-Path $RepositoryRoot $rootFile
  if (Test-Path -LiteralPath $path -PathType Leaf) {
    $ownedFiles.Add((Get-Item -LiteralPath $path))
  }
}
$ownedSourceRoot = Join-Path $RepositoryRoot 'Robin1984'
Get-ChildItem -LiteralPath $ownedSourceRoot -Filter '*.lean' -File -Recurse |
  ForEach-Object { $ownedFiles.Add($_) }
$mathlibFacadePath = Join-Path $RepositoryRoot 'Robin1984\Mathlib.lean'
if (-not (Test-Path -LiteralPath $mathlibFacadePath -PathType Leaf)) {
  $failures.Add('Missing required Mathlib candidate facade: Robin1984/Mathlib.lean')
}
$mathlibManifestPath = Join-Path $RepositoryRoot 'MATHLIB_PORTING.md'
$mathlibManifestLines = @()
if (-not (Test-Path -LiteralPath $mathlibManifestPath -PathType Leaf)) {
  $failures.Add('Missing required Mathlib candidate inventory: MATHLIB_PORTING.md')
} else {
  $mathlibManifestLines = @(Get-Content -LiteralPath $mathlibManifestPath)
}
$moduleNameFixture = 'Robin1984\Mathlib\Example.lean'
$moduleNameFixtureResult = $moduleNameFixture.Substring(
  0,
  $moduleNameFixture.Length - '.lean'.Length
).Replace('\', '.').Replace('/', '.')
if ($moduleNameFixtureResult -cne 'Robin1984.Mathlib.Example') {
  throw "Lean module-name normalization fixture failed: $moduleNameFixtureResult"
}

foreach ($file in $ownedFiles | Sort-Object FullName) {
  $relative = [IO.Path]::GetRelativePath($RepositoryRoot, $file.FullName)
  $sourceText = [IO.File]::ReadAllText($file.FullName)
  $imports = @(Get-DirectImports -Path $file.FullName)
  if (-not $relative.EndsWith('.lean', [System.StringComparison]::Ordinal)) {
    throw "Owned Lean path lacks the expected suffix: $relative"
  }
  $module = $relative.Substring(0, $relative.Length - '.lean'.Length).Replace('\', '.').Replace('/', '.')
  if ($module.EndsWith('.', [System.StringComparison]::Ordinal) -or
      $module.Contains('\') -or $module.Contains('/')) {
    throw "Owned Lean path did not normalize to a module name: $relative => $module"
  }
  $isMathlibCandidate = $module -ceq $mathlibCandidateRoot -or
    $module.StartsWith("$mathlibCandidateRoot.", [System.StringComparison]::Ordinal)

  if (-not $isMathlibCandidate) {
    foreach ($pair in $compatibilityUnfoldPairs) {
      $legacyName = $pair[0]
      $candidateName = $pair[1]
      $unfoldPattern = "(?m)^\s*unfold\s+[^`r`n]*\b$([regex]::Escape($legacyName))\b[^`r`n]*$"
      foreach ($unfoldMatch in [regex]::Matches($sourceText, $unfoldPattern)) {
        if (-not $unfoldMatch.Value.Contains($candidateName)) {
          $failures.Add("${relative}: unfold of compatibility alias '$legacyName' must also unfold '$candidateName'")
        }
      }
    }
  }

  if ($relative -in @('Challenge.lean', 'Solution.lean') -and
      $sourceText -notmatch '(?m)^set_option autoImplicit false\s*$') {
    $failures.Add("${relative}: the Palomar theorem boundary must disable autoImplicit")
  }
  if ($relative -in @('Challenge.lean', 'Solution.lean') -and
      'Mathlib.NumberTheory.LSeries.RiemannZeta' -notin $imports) {
    $failures.Add("${relative}: the Palomar theorem boundary must directly import Mathlib.NumberTheory.LSeries.RiemannZeta")
  }
  if ($relative -ceq 'Challenge.lean') {
    foreach ($ownedImport in Get-OwnedImportsInClosure -RootImports $imports) {
      $failures.Add("${relative}: Palomar Challenge closure contains project module '$ownedImport'")
    }
  }

  if ($isMathlibCandidate) {
    foreach ($import in $imports) {
      if (Test-OwnedModuleName -Module $import) {
        if (-not ($import -ceq $mathlibCandidateRoot -or
            $import.StartsWith("$mathlibCandidateRoot.", [System.StringComparison]::Ordinal))) {
          $failures.Add("${relative}: Mathlib candidate imports project module '$import'")
        }
        continue
      }
      $allowedExternal = @($mathlibAllowedExternalPrefixes | Where-Object {
        $import.StartsWith($_, [System.StringComparison]::Ordinal)
      }).Count -ne 0
      if (-not $allowedExternal) {
        $failures.Add("${relative}: Mathlib candidate imports non-Mathlib dependency '$import'")
      }
    }

    if ($module -cne $mathlibCandidateRoot) {
      foreach ($marker in $mathlibHeaderMarkers) {
        if (-not $sourceText.Contains($marker)) {
          $failures.Add("${relative}: Mathlib candidate missing source marker '$marker'")
        }
      }
      $body = $sourceText -replace '(?m)^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import(?:\s+all)?\s+[A-Za-z0-9_''\.]+\s*$', ''
      if ($body -match '\bRobin1984\b') {
        $failures.Add("${relative}: Mathlib candidate body references project namespace Robin1984")
      }
      $manifestNeedle = [string]::Concat('`', $module, '`')
      $manifestRows = @($mathlibManifestLines | Where-Object { $_.Contains($manifestNeedle) })
      if ($manifestRows.Count -ne 1) {
        $failures.Add("${relative}: expected exactly one MATHLIB_PORTING.md inventory row")
      } else {
        $manifestRow = $manifestRows[0]
        if (-not $manifestRow.Contains('`Mathlib/')) {
          $failures.Add("${relative}: inventory row lacks a proposed Mathlib path")
        }
        $hasReadinessState = @($mathlibReadinessStates | Where-Object {
          $manifestRow.Contains($_)
        }).Count -ne 0
        if (-not $hasReadinessState) {
          $failures.Add("${relative}: inventory row lacks a recognized readiness state")
        }
      }
    }
  }

  $seen = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
  )
  foreach ($import in $imports) {
    if (-not $seen.Add($import)) {
      $failures.Add("${relative}: duplicate import '$import'")
    }
    if (Test-BroadImport -Module $import) {
      $failures.Add("${relative}: broad import '$import' is forbidden")
    }
    if ($null -eq (Resolve-ModulePath -Module $import)) {
      $failures.Add("${relative}: import '$import' does not resolve to a pinned source module")
    }
  }

  $sortedImports = @($imports | Sort-Object -CaseSensitive)
  if ([string]::Join("`n", $imports) -cne [string]::Join("`n", $sortedImports)) {
    $failures.Add("${relative}: imports must be in ordinal lexicographic order")
  }

  foreach ($candidate in $imports) {
    foreach ($provider in $imports) {
      if ($candidate -ceq $provider) {
        continue
      }
      if (-not (Test-OwnedModuleName -Module $candidate) -or
          -not (Test-OwnedModuleName -Module $provider)) {
        continue
      }
      if (Test-TransitivelyImports -Provider $provider -Candidate $candidate) {
        $failures.Add("${relative}: import '$candidate' is transitively supplied by '$provider'")
        break
      }
    }
  }
}

if ($failures.Count -ne 0) {
  $failures | Sort-Object -Unique | ForEach-Object {
    [Console]::Error.WriteLine($_)
  }
  throw "Import lint failed with $($failures.Count) finding(s)."
}

Write-Host "Import lint passed for $($ownedFiles.Count) owned Lean files."
