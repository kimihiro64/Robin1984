# Research backlog

Run the backlog in the existing Robin1984 checkout. The explorer at
[Backlog](lmfdb-explorer/index.html#backlog) reads the generated browser
snapshot. The local work database is `.git/lmfdb-backlog.sqlite`. It
holds imported identifiers, source receipts, crosswalks, decisions, and
decision history. Keep that file with the repository during backups or
migration. The site publishes the bounded progress snapshot, with the
canonical evidence and large inventory retained in Robin1984.

## Work a queue

Using Node 24, let `backlog` below stand for invoking the resolved Node
executable with `docs/lmfdb-explorer/backlog.mjs`.

1. Run `backlog next` to get one candidate per active queue before
   additional candidates from the same queue. For a single family use
   `backlog next --family dirichlet`.
2. Read `backlog show L:<label>`. Verify the identity including its actual
   origin, analytic normalization and any other labels for the same
   function.
3. Work the first unresolved stage. The gates are identity, local data,
   triangle, location, multiplicity and ideal assessment.
4. Save the decision with the evidence reference and exact scope.
5. Run `backlog status` for counted progress or `backlog export` to
   regenerate the static explorer snapshot. Run `backlog check` to
   confirm the snapshot matches the work database before publishing.

A reviewed catalogue entry attaches to an imported identifier and initializes
its stages when there are no existing review decisions. If work on that
identifier has already been recorded, use `backlog record` to advance its
stages with the new evidence. Catalogue synchronization preserves recorded
reviews and writes new catalogue decisions to the journal.

For example, after reading and verifying the source for a new identifier:

```text
backlog record L:1-3-3.2-r1-0-0 --stage identity --status done --level source --evidence https://www.lmfdb.org/L/1/3/3.2/r1/0/0
```

Use `--status blocked --note "exact missing input"` to stop that row and
give the researcher a concrete task. Give a recurring missing provider a
stable `--blocker` key. The site counts the number of inventoried records
at each shared blocker, and `backlog next` keeps advancing other cases.
After finding a provider, verify its hypotheses on each affected label
before advancing it. Use `--status not-applicable` only for a documented
multiplicity or ideal assessment.

`--level source`, `prose`, `lean-family` and `lean-instance` distinguish
the type of evidence. A family theorem requires a separate identification
of the concrete function. Use `--scope signed-divisor` for the two-sided
Artin alternative. It can supply location and matching multiplicity
evidence while the ordinary one-sided triangle remains blocked. A
successful criterion tests the zero assertion and counts as a reviewed
equivalence without settling the corresponding RH assertion. Decisions
are stored with before and after values and listed by `backlog journal`.

| Stage | Evidence to record |
| --- | --- |
| Identity | LMFDB identifier, actual function and origin crosswalk, including dual where needed. |
| Local data | Exact unramified formula, every bad factor, pole order, archimedean normalization and analytic provider. |
| Triangle | Both sides of the triangular equivalence and the proof or named obstruction. |
| Location | Actual downstream arithmetic predicate, domain, forward and reverse consequences, and any factor assumptions. |
| Multiplicity | Individual signal and central order, prescribed ordinates, proof and scope. |
| Ideal | Exact field, ideal inequality and factor scope, or the precise missing transfer. |

## Intake and checkpoints

### Precomputed labels

Choose a named run with an exclusive lower bound and inclusive upper
bound. Omit `--after` to begin at ID 1. Each page uses an increasing range
of source IDs and commits the rows, receipt hash and cursor in one
transaction. A failed page leaves the saved cursor intact. The canonical
identifier is the LMFDB L-function label. The numeric API ID is a traversal
cursor. The public API timed out on an unrestricted descending-ID query.
A published record count does not specify the upper cursor. Use bounded
ranges for progress or a pinned search export or SQL snapshot for an exact
inventory.

```text
backlog scan --run pilot-precomputed --through 100 --pages 1
backlog scan --run precomputed-101-300 --after 100 --through 300 --pages 2
```

Use the live API for small batches. The public API returns up to 100
results per request. Large inventories fit the same import path from
LMFDB search downloads or its read-only mirror. The LMFDB can change
live IDs and contents. A completed run records traversal of its requested
bound. A reproducible census needs a pinned source export.

[LMFDB API](https://www.lmfdb.org/api/) ·
[LMFDB access options and SQL mirror](https://www.lmfdb.org/api/options)

### Dynamic and overlapping families

The [family registry](lmfdb-explorer/backlog-families.json) lists the
published degree 1–40 cohorts and the fallback queue for other
precomputed labels. Dynamic Dedekind, Maass and Artin entries can be
imported from their origin searches or source exports. Use normalized
UTF-8 JSONL batches of at most 10,000 records. The first line gives the
run, the exact LMFDB export URL and the subsequent row count.

```json
{"run":"cubic-fields-2026-11","source":"https://www.lmfdb.org/NumberField/?degree=3","records":1}
{"key":"NumberField:3.1.23.1","name":"Discriminant −23 cubic","url":"https://www.lmfdb.org/NumberField/3.1.23.1","family":"dedekind3","degree":3}
```

Import with `backlog import --file <batch.jsonl>`. Repeating an identical
batch has no effect. One identifier can belong to several source runs
and is counted once in its primary work queue. Record a verified
crosswalk with
`backlog link <origin-key> <canonical-L-key> --evidence <reference>`.
The merge preserves memberships and existing decisions and rejects
conflicting reviews. Keep a dual as its own identifier. Use `Origin:`
with the exact typed origin path when the row lacks a canonical
L-function identifier.

Published source populations are reported alongside primary queue counts
because the same L-function can appear in several source populations.
The two kinds of count serve different purposes. Imported LMFDB metadata
is attributed to LMFDB under its CC BY-SA data license.

[Published coverage](https://www.lmfdb.org/L/Completeness) ·
[Data license](https://www.lmfdb.org/api/options)

## GitHub Pages releases

Run the catalogue and backlog checks on the staged source, together with
`docs/lmfdb-explorer/verify-389-center.mjs` for releases that change the
389.a1 proof or certificate. Run `verify-dirichlet-center.mjs 11` when
changing the conductor-11 results or their shared interval verifier.
Then commit in Robin1984.
The Pages source is the root of the separate
`gh-pages` branch in the same repository. Resolve the current remote
branch SHA and pass it as `--parent` to
`docs/lmfdb-explorer/prepare-pages.mjs`, together with
`--git` and the verified absolute Git executable. The script constructs
a fast-forward candidate from the committed static files and prints its
SHA without switching checkouts. Push that candidate with a lease on the
observed remote SHA. Verify that GitHub Pages built the pushed commit and
that the hosted catalogue and backlog match the committed assets.

Check API checkpoints by numeric start and end ID. Run names are labels.
Confirm that the newly completed range appears in order and that its stated
cursor equals the database checkpoint before reporting the covered range.

When publishing a catalogue update, check the generated HTML references and
exercise the new release in a browser that has already loaded the previous
release. The preparation script versions the browser asset URLs by Git blob
ID. A successful download of an unversioned asset does not verify what a
warm browser rendered. Confirm the visible case and queue counts after
loading the new HTML. The host can retain previous HTML for its cache
lifetime, so a revision query on the page URL can be used to obtain the
current document during release verification.

## First review batch

The pilot includes the existing catalogue cases. The first precomputed
run takes source IDs 1 through 100. The first new rank-one task is
`L:1-3-3.2-r1-0-0`. The queue keeps existing conditional
ideal assessments moving and continues to surface the queued 389.a1
and GL₃ Maass records. The even icosahedral case retains its named
one-sided holomorphy blocker and its signed-divisor evidence.
