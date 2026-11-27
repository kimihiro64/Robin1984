"use strict";

const statusNames = {
  done: "Equivalence derived",
  blocked: "One-sided blocked",
  unreviewed: "Awaiting review",
};
const formatNumber = new Intl.NumberFormat("en");
const byId = (id) => document.getElementById(id);
const filters = ["search", "status", "family", "degree"].map(byId);
const cutoffControl = byId("cutoff");
const cutoffOutput = byId("cutoff-value");
let catalog;
let selected;
let demoCases;
let series;

function element(tag, value, className) {
  const node = document.createElement(tag);
  if (value !== undefined) node.textContent = value;
  if (className) node.className = className;
  return node;
}

function link(title, url) {
  const node = element("a", title);
  node.href = url;
  return node;
}

function badge(status) {
  return element("span", statusNames[status], "badge " + status);
}

function stats() {
  const totals = [
    ["", "Tracked records", "Pilot inventory", catalog.entries.length],
    ["done", "Equivalences derived", catalog.entries.filter((row) => row.proof === "Lean provider").length + " backed by Lean family providers", 0],
    ["blocked", "One-sided blocked", "Exact obligation recorded", 0],
    ["unreviewed", "Awaiting review", "In the pilot queue", 0],
  ];
  byId("statistics").replaceChildren(...totals.map(([key, label, note, count]) => {
    const card = element("button", undefined, "stat");
    card.type = "button";
    card.setAttribute("aria-pressed", String(byId("status").value === key));
    const value = key ? catalog.entries.filter((row) => row.status === key).length : count;
    card.append(element("strong", formatNumber.format(value)), element("span", label), element("small", note));
    card.addEventListener("click", () => {
      for (const control of filters) control.value = "";
      byId("status").value = key;
      renderCatalog();
      byId("catalog").scrollIntoView();
    });
    return card;
  }));
}

function formulaText(value) {
  const display = element("div", undefined, "criterion-formula");
  let start = 0;
  for (const hit of value.matchAll(/∑_\{([^}]+)\}/g)) {
    const sum = element("span", "∑", "sum-symbol");
    sum.append(element("sub", hit[1]));
    display.append(value.slice(start, hit.index), sum);
    start = hit.index + hit[0].length;
  }
  display.append(value.slice(start));
  return display;
}

function criterionCard(data) {
  const card = element("section", undefined, "criterion-card");
  card.append(element("h4", data.title));
  if (data.hypothesis) card.append(element("p", data.hypothesis, "criterion-hypothesis"));

  const statements = element("div", undefined, "criterion-statements");
  const zeroSide = element("div", undefined, "criterion-side");
  zeroSide.append(element("h5", "Zero statement"), element("p", data.zeros));
  const arithmeticSide = element("div", undefined, "criterion-side arithmetic");
  arithmeticSide.append(element("h5", "Arithmetic statement"), element("p", data.arithmetic));
  if (data.formula) arithmeticSide.append(formulaText(data.formula));
  const iff = element("div", undefined, "criterion-iff");
  const symbol = element("span", "⟺");
  symbol.setAttribute("aria-hidden", "true");
  iff.append(symbol, element("span", "if and only if", "sr-only"));

  statements.append(zeroSide, iff, arithmeticSide);
  card.append(statements);
  for (const note of data.notes ?? []) {
    const line = element("p", undefined, "criterion-note");
    line.append(...formulaText(note).childNodes);
    card.append(line);
  }
  if (data.links?.length) {
    const sources = element("div", undefined, "actions");
    for (const [title, url] of data.links) sources.append(link(title, url));
    card.append(sources);
  }
  return card;
}

function multiplicityNotation(individual, excluded) {
  const notes = element("details", undefined, "criterion-notation");
  const excludedText = excluded
    ? "Hₐ,E is Hₐ with the frequency at u = 0 removed."
    : "E is empty, so Hₐ,E = Hₐ.";
  notes.append(
    element("summary", "Multiplicity notation"),
    formulaText(individual),
    element("p", "Use this individual remainder to form A(t) = e⁻ᵗᐟ² R(eᵗ) for t ≥ 0, extended by zero for t < 0."),
    element("p", "Hₐ(t) = ∫ℝ kₐ(v) A(t − v) dv, with kₐ(v) = (v²/(4a²) − v/a + 3/4 − 1/(2a)) e⁻ᵛ²ᐟ⁽⁴ᵃ⁾ / √(4πa)."),
    element("p", "c₁(0) = lim(T→∞) (1/T) ∫₀ᵀ H₁(t) dt. " + excludedText),
    link("Proof and kernel normalization", "../LMFDB.md"),
  );
  return notes;
}

function renderEquivalences(row) {
  const section = element("div", undefined, "equivalences");
  const eq = row.equivalences;
  if (!eq) {
    section.append(element("p", "No individual equivalence has been reviewed for this label.", "criterion-pending"));
    return section;
  }
  for (const endpoint of eq.arithmeticEndpoints) {
    const notes = endpoint.note ? [endpoint.note] : [];
    if (endpoint === eq.arithmeticEndpoints[0] && eq.idealField && endpoint.hypothesis) {
      const field = catalog.correctedIdealRobin.fields[eq.idealField];
      notes.push("The unconditional fieldwise equivalence is to " + field.zeros.charAt(0).toLowerCase() + field.zeros.slice(1));
    }
    section.append(criterionCard({ ...endpoint, notes }));
  }

  const { location } = eq;
  const orderFormula = "U(t,δ) = −δs ∫₁∞ [B(x) − mx] x⁻ˢ⁻¹ dx, where s = 1/2 + it + δ.";
  const orderNotes = [
    "B(x) = ∑_{pʲ ≤ x} a(p,j) log p from the individual local factors. Use m = " + row.pole + ".",
    row.coef,
  ];
  if (eq.signed) {
    section.append(
      criterionCard({
        title: "Holomorphy and the critical line",
        zeros: "Λρ is holomorphic and every zero lies on Re s = 1/2.",
        arithmetic: "The Frobenius trace bound above holds, and " + eq.signed.location,
        formula: eq.signed.formula,
        notes: orderNotes,
      }),
      criterionCard({
        title: "Signed-order test for simplicity",
        hypothesis: "Assuming the Frobenius trace bound above",
        zeros: "Λρ is holomorphic and every zero is simple.",
        arithmetic: eq.signed.simplicity,
        formula: eq.signed.formula,
        notes: orderNotes,
      }),
    );
  } else {
    const order = eq.centralOrder;
    const excluded = order > 1;
    const penalty = order === 0 ? "|c₁(0)|²" : "|c₁(0) − " + order + "|²";
    const zeros = "Every noncentral zero of " + location.subject + " is simple, and the order at s = 1/2 is exactly " + order + ".";
    const multiplicity = criterionCard({
      title: "Multiplicity and central order",
      hypothesis: "Assuming the stated critical-line hypothesis",
      zeros,
      arithmetic: "For each real t ≠ 0, Re U(t,δ) < 3/2 eventually as δ decreases to zero. At t = 0, |Re U(0,δ) − " + order + "| < 1/2 eventually.",
      formula: orderFormula,
      notes: [...orderNotes, row.orders],
    });
    const gaussian = element("details", undefined, "criterion-notation");
    gaussian.append(
      element("summary", "Equivalent Gaussian multiplicity test"),
      element("p", "Set J = {0}, d(0) = " + order + " and E = " + (excluded ? "{0}." : "∅.")),
      formulaText("limsup(T→∞) (1/T) ∫₀ᵀ |H₁,E(t)|² dt + " + penalty + " ≤ limsup(t→∞) Re H₂,E(t)."),
      multiplicityNotation(eq.individual ?? location.remainder, excluded),
    );
    multiplicity.append(gaussian);
    section.append(multiplicity);
  }

  const absolute = location.mode === "absolute";
  const proof = element("details", undefined, "criterion-notation triangular-proof");
  proof.append(
    element("summary", "Triangular criterion and derivation"),
    criterionCard({
      title: absolute ? "Two-sided triangular bound" : "One-sided triangular bound",
      zeros: absolute
        ? "Every zero and pole of " + location.subject + " lies on Re s = 1/2."
        : "Every zero of " + location.subject + " lies on Re s = 1/2.",
      arithmetic: "There exist C > 0 and X ≥ 1 such that for every real x ≥ X, "
        + (absolute ? "|R(x)| ≤ C√x." : "R(x) ≤ C√x."),
      formula: location.remainder,
      notes: [row.coef, location.note].filter(Boolean),
    }),
    link("Proof of the arithmetic specializations", "../LMFDB.md"),
  );
  for (const extra of eq.additional ?? []) {
    proof.append(criterionCard({ ...extra, notes: extra.note ? [extra.note] : [] }));
  }
  section.append(proof);
  return section;
}

function renderBacklog() {
  const backlog = globalThis.LMFDB_BACKLOG;
  if (!backlog) {
    byId("backlog-caption").textContent = "The backlog snapshot could not be loaded.";
    return;
  }
  const format = (n) => formatNumber.format(n);
  const stages = new Map(backlog.stages.map((stage) => [stage.id, stage.name]));
  const families = new Map(backlog.families.map((family) => [family.id, family.name]));
  const statuses = [["complete", "Review complete"], ["in-progress", "In progress"], ["blocked", "Blocked"], ["unreviewed", "Unreviewed"]];
  byId("backlog-caption").textContent = format(backlog.total) + " inventoried identifiers.";
  byId("backlog-totals").replaceChildren(...statuses.map(([state, label]) => {
    const item = element("div");
    item.append(element("dt", label), element("dd", format(backlog.state[state])));
    return item;
  }));
  const tableRow = (label, values) => {
    const row = element("tr");
    const heading = element("th", label);
    heading.scope = "row";
    row.append(heading, ...values.map((value) => element("td", value === null ? "—" : format(value))));
    return row;
  };
  byId("backlog-stages").replaceChildren(...backlog.stages.map((stage) =>
    tableRow(stage.name, [stage.done, stage.alternate, stage.blocked, stage["not-applicable"], stage.unreviewed])));
  byId("backlog-families").replaceChildren(...backlog.families.map((family) =>
    tableRow(family.name, [family.published, ...statuses.map(([state]) => family.counts[state])])));
  const listItem = (job, description) => {
    const li = element("li");
    const target = job.catalog_id ? "?entry=" + encodeURIComponent(job.catalog_id) + "#catalog" : job.url;
    li.append(link(job.name, target), element("span", description));
    return li;
  };
  byId("backlog-next").replaceChildren(...backlog.queue.map((job) =>
    listItem(job, stages.get(job.phase) + " · " + families.get(job.family))));
  byId("backlog-blocked").replaceChildren(...backlog.blocked.map((job) =>
    listItem(job, stages.get(job.phase) + " · " + job.note)));
  byId("backlog-shared").textContent = backlog.sharedBlockers.map(({ blocker, affected }) =>
    blocker.replaceAll("-", " ") + " affects " + format(affected) + (affected === 1 ? " record." : " records.")
  ).join(" ");
  byId("backlog-runs").replaceChildren(...backlog.runs.map((run) => {
    const cursor = run.mode === "api"
      ? " · IDs " + format(run.start_id + 1) + "–" + format(run.through_id) + " · reached " + format(run.cursor)
      : "";
    return element("li", run.id + " · " + format(run.unique_labels) + " identifiers" + cursor);
  }));
}

function renderIdealFields() {
  const records = Object.entries(catalog.correctedIdealRobin.fields).map(([key, field]) => {
    const tr = element("tr");
    const name = element("th", field.field);
    name.scope = "row";
    const labels = element("td");
    const entries = catalog.entries.filter((row) => row.equivalences?.idealField === key);
    for (const row of entries) {
      const item = element("div");
      item.append(link(row.name, "?entry=" + encodeURIComponent(row.id) + "#catalog"));
      labels.append(item);
    }
    tr.append(name, element("td", String(field.discriminant)), element("td", field.zeros), labels);
    return tr;
  });
  byId("ideal-field-records").replaceChildren(...records);
}

function chooseRecord(row, updateUrl) {
  selected = row;
  for (const item of byId("records").rows) {
    const active = item.dataset.id === row.id;
    item.dataset.active = String(active);
    item.querySelector("button").setAttribute("aria-pressed", String(active));
  }
  if (updateUrl) {
    const current = new URL(window.location.href);
    current.searchParams.set("entry", row.id);
    history.replaceState(null, "", current);
  }
  const detail = byId("detail");
  const meta = element("div", undefined, "sub-detail");
  meta.append(badge(row.status), element("span", row.proof));
  const body = element("dl");
  const fields = [
    ["Origin labels", row.origins.join(" · ")],
    ["Unitary completion", row.completion],
    ["Evidence for the criterion", row.basis],
    ["Central order", row.center],
    [row.status === "blocked" ? "Blocking input" : "Remaining work", row.obligation],
  ];
  for (const [label, value] of fields) {
    if (!value) continue;
    body.append(element("dt", label), element("dd", value));
  }
  const sources = element("div", undefined, "actions");
  sources.append(link("LMFDB record", row.url));
  if (row.dual) {
    const destination = new URL(window.location.href);
    destination.searchParams.set("entry", row.dual);
    destination.hash = "catalog";
    sources.append(link("Contragredient", destination.href));
  }
  for (const [title, url] of row.sources ?? []) sources.append(link(title, url));
  detail.replaceChildren(meta, element("h3", row.name), element("p", row.id, "record-id"), renderEquivalences(row), body, sources);
  if (updateUrl && window.matchMedia("(max-width: 760px)").matches) detail.scrollIntoView({ block: "start" });
}

function renderCatalog() {
  const [search, status, family, degree] = filters.map((field) => field.value);
  const terms = search.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
  const matches = catalog.entries.filter((row) => {
    const searchable = [row.id, row.name, row.family, ...row.origins].join(" ").toLocaleLowerCase();
    return terms.every((term) => searchable.includes(term))
      && (!status || row.status === status)
      && (!family || row.family === family)
      && (!degree || String(row.degree) === degree);
  });
  byId("results").textContent = matches.length + " of " + catalog.entries.length + " records";
  const tableRows = matches.map((row) => {
    const item = element("tr");
    item.dataset.id = row.id;
    const first = element("td");
    const button = element("button", row.name, "record");
    button.type = "button";
    button.setAttribute("aria-pressed", "false");
    button.addEventListener("click", () => chooseRecord(row, true));
    first.append(button, element("span", row.id, "record-id"));
    const state = element("td");
    state.append(badge(row.status));
    item.append(first, element("td", row.degree), state);
    return item;
  });
  byId("records").replaceChildren(...tableRows);
  if (matches.length) chooseRecord(matches.includes(selected) ? selected : matches[0], false);
  else byId("detail").replaceChildren(element("h3", "No matching records"), element("p", "Try another label or reset the filters."));
  stats();
}

function renderCohorts() {
  byId("snapshot-link").href = catalog.snapshotSource;
  const applied = catalog.entries.filter((row) => row.multiplicity === "applied").length;
  const signed = catalog.entries.filter((row) => row.multiplicity === "signed").length;
  const unreviewed = catalog.entries.filter((row) => row.multiplicity === "unreviewed").length;
  byId("proof-progress").textContent = "Multiplicity: " + applied + " individual tests specified · "
    + signed + " signed-order extension · " + unreviewed + " awaiting review. Catalog snapshot " + catalog.asOf + ".";
  byId("cohorts").replaceChildren(...catalog.cohorts.map((cohort) => {
    const included = catalog.entries.filter((row) => row.cohort === cohort.id);
    const done = included.filter((row) => row.status === "done").length;
    const blocked = included.filter((row) => row.status === "blocked").length;
    const block = element("article", undefined, "cohort");
    block.append(
      element("h3", cohort.name),
      element("strong", formatNumber.format(cohort.total)),
      element("p", done + " derived · " + blocked + " blocked"),
      element("p", formatNumber.format(cohort.total - done - blocked) + " without individual review"),
    );
    return block;
  }));
}

function primesThrough(limit) {
  const composite = new Uint8Array(limit + 1);
  const primes = [];
  for (let candidate = 2; candidate <= limit; candidate += 1) {
    if (composite[candidate]) continue;
    primes.push(candidate);
    for (let multiple = candidate * candidate; multiple <= limit; multiple += candidate) {
      composite[multiple] = 1;
    }
  }
  return primes;
}

function cubicCycle(prime) {
  let roots = 0;
  for (let value = 0; value < prime; value += 1) {
    if ((value ** 3 - value - 1) % prime === 0) roots += 1;
  }
  if (roots === 3) return 1;
  if (roots === 1) return 2;
  if (roots === 0) return 3;
  throw new Error("Unexpected unramified splitting type");
}

function curve37Trace(prime) {
  if (prime === 2) return -2;
  const squareCounts = new Uint8Array(prime);
  for (let value = 0; value < prime; value += 1) squareCounts[(value * value) % prime] += 1;
  let points = 1;
  for (let value = 0; value < prime; value += 1) {
    const discriminant = (1 + 4 * (value ** 3 - value)) % prime;
    points += squareCounts[discriminant];
  }
  return prime + 1 - points;
}

function localTrace(caseName, prime) {
  switch (caseName) {
    case "zeta":
      return () => 1;
    case "beta": {
      const value = [0, 1, 0, -1][prime % 4];
      return (power) => value ** power;
    }
    case "quartic": {
      const exponent = [-1, 0, 1, 3, 2][prime % 5];
      return (power) => exponent < 0 ? 0 : 2 * [1, 0, -1, 0][(power * exponent) % 4];
    }
    case "s3":
    case "cubic": {
      const offset = caseName === "cubic" ? 1 : 0;
      if (prime === 23) return () => 1 + offset;
      const cycle = cubicCycle(prime);
      return (power) => (power % cycle === 0 ? 2 : cycle === 2 ? 0 : -1) + offset;
    }
    case "curve37": {
      if (prime === 37) return (power) => (-1 / Math.sqrt(37)) ** power;
      const first = curve37Trace(prime) / Math.sqrt(prime);
      let previous = 2;
      let current = first;
      return () => {
        const value = current;
        [previous, current] = [current, first * current - previous];
        return value;
      };
    }
    default:
      throw new Error("Unknown sample rule");
  }
}

function triangularSamples(row, cutoff) {
  const powers = [];
  for (const prime of primesThrough(cutoff)) {
    const trace = localTrace(row.demo, prime);
    for (let power = 1, norm = prime; norm <= cutoff; power += 1, norm *= prime) {
      powers.push([norm, Math.log(prime) * trace(power)]);
    }
  }
  powers.sort((left, right) => left[0] - right[0]);
  let next = 0;
  let coefficientSum = 0;
  let weightedSum = 0;
  const samples = Array.from({ length: 121 }, (_, index) => {
    const x = index === 120 ? cutoff : 2 + (cutoff - 2) * index / 120;
    while (next < powers.length && powers[next][0] <= x) {
      const [norm, coefficient] = powers[next];
      coefficientSum += coefficient;
      weightedSum += norm * coefficient;
      next += 1;
    }
    const y = (row.pole * x / 2 - coefficientSum + weightedSum / x) / Math.sqrt(x);
    return { x, y };
  });
  if (samples[0].x !== 2 || samples.at(-1).x !== cutoff || next !== powers.length) {
    throw new Error("Sample domain did not reach the displayed maximum");
  }
  return { samples, slots: powers.length };
}

function drawChart() {
  if (!series) return;
  const canvas = byId("chart");
  const width = canvas.clientWidth;
  const height = canvas.clientHeight;
  if (!width || !height) return;
  const pixelRatio = Math.min(window.devicePixelRatio ?? 1, 2);
  canvas.width = Math.round(width * pixelRatio);
  canvas.height = Math.round(height * pixelRatio);
  const ctx = canvas.getContext("2d");
  ctx.scale(pixelRatio, pixelRatio);
  const plot = { left: 49, top: 16, right: width - 17, bottom: height - 36 };
  const yVals = series.samples.map((point) => point.y);
  const low = Math.min(0, ...yVals);
  const high = Math.max(0, ...yVals);
  const padding = (high - low || 1) * .08;
  const lo = low - padding;
  const hi = high + padding;
  const maxX = series.samples.at(-1).x;
  const toX = (x) => plot.left + (x - 2) / (maxX - 2) * (plot.right - plot.left);
  const toY = (y) => plot.bottom - (y - lo) / (hi - lo) * (plot.bottom - plot.top);
  ctx.font = "12px Arial";
  ctx.textAlign = "right";
  ctx.fillStyle = "#536174";
  for (let tick = 0; tick <= 4; tick += 1) {
    const val = lo + (hi - lo) * tick / 4;
    const y = toY(val);
    ctx.strokeStyle = "#dce4eb";
    ctx.beginPath();
    ctx.moveTo(plot.left, y);
    ctx.lineTo(plot.right, y);
    ctx.stroke();
    ctx.fillText(val.toFixed(2), plot.left - 7, y + 4);
  }
  ctx.strokeStyle = "#889aab";
  ctx.beginPath();
  ctx.moveTo(plot.left, toY(0));
  ctx.lineTo(plot.right, toY(0));
  ctx.stroke();
  ctx.textAlign = "center";
  for (let tick = 0; tick <= 4; tick += 1) {
    const val = Math.round(2 + (maxX - 2) * tick / 4);
    ctx.fillText(formatNumber.format(val), toX(val), plot.bottom + 19);
  }
  ctx.strokeStyle = "#1b7b78";
  ctx.lineWidth = 2.3;
  ctx.beginPath();
  series.samples.forEach((point, index) => {
    if (index === 0) ctx.moveTo(toX(point.x), toY(point.y));
    else ctx.lineTo(toX(point.x), toY(point.y));
  });
  ctx.stroke();
}

function renderDemo() {
  const row = demoCases.find((entry) => entry.id === byId("demo").value);
  const cutoff = Number(cutoffControl.value);
  if (!Number.isInteger(cutoff) || cutoff < Number(cutoffControl.min) || cutoff > Number(cutoffControl.max)) {
    throw new Error("Invalid sample maximum");
  }
  series = triangularSamples(row, cutoff);
  cutoffOutput.value = String(cutoff);
  const last = series.samples.at(-1);
  byId("endpoint").textContent = last.y.toFixed(5);
  byId("slots").textContent = formatNumber.format(series.slots);
  byId("chart-text").textContent = "Finite illustration for " + row.name + ", from x=2 to x=" + formatNumber.format(cutoff) + ". The sample gives no bound beyond this interval.";
  drawChart();
}

function start() {
  catalog = globalThis.LMFDB_CATALOG;
  if (!catalog) throw new Error("Catalogue data could not be loaded. Keep catalog-data.js beside index.html.");
  renderIdealFields();
  renderBacklog();
  const initial = new URL(window.location.href).searchParams.get("entry");
  selected = catalog.entries.find((row) => row.id === initial)
    ?? catalog.entries.find((row) => row.id === "2-23-23.22-c0-0-0");
  for (const family of [...new Set(catalog.entries.map((row) => row.family))].sort()) {
    byId("family").add(new Option(family, family));
  }
  for (const degree of [...new Set(catalog.entries.map((row) => row.degree))].sort((a, b) => a - b)) {
    byId("degree").add(new Option(degree, degree));
  }
  for (const field of filters) field.addEventListener(field.id === "search" ? "input" : "change", renderCatalog);
  byId("reset").addEventListener("click", () => {
    for (const field of filters) field.value = "";
    renderCatalog();
  });
  demoCases = catalog.entries.filter((row, index, entries) =>
    row.demo && entries.findIndex((entry) => entry.demo === row.demo) === index);
  for (const row of demoCases) {
    byId("demo").add(new Option(row.demo === "quartic" ? "Quartic characters mod 5 (paired)" : row.name, row.id));
  }
  byId("demo").addEventListener("change", renderDemo);
  cutoffControl.addEventListener("input", renderDemo);
  new ResizeObserver(drawChart).observe(byId("chart"));
  renderCatalog();
  renderCohorts();
  renderDemo();
}

try {
  start();
} catch (error) {
  byId("results").textContent = error.message;
  console.error(error);
}
