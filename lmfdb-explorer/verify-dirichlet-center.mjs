import assert from "node:assert/strict";

// Certify central nonvanishing for primitive characters of odd prime-power
// conductor. Enclosures are outward-rounded integers and include the
// summation-by-parts error beyond the last complete period.

const modulus = Number(process.argv[2] ?? "11");
const periods = Number(process.argv[3] ?? "1024");
const terms = modulus * periods;
assert.ok(Number.isSafeInteger(modulus) && modulus >= 3 && modulus % 2 === 1);
assert.ok(Number.isSafeInteger(modulus * modulus) && Number.isSafeInteger(terms));
assert.ok(Number.isSafeInteger(periods) && periods >= 1);
const scale = 10n ** 24n;
const floorDiv = (n, d) => n >= 0n ? n / d : -((-n + d - 1n) / d);
const ceilDiv = (n, d) => -floorDiv(-n, d);

function primeFactors(n) {
  const out = [];
  for (let p = 2; p * p <= n; ++p) {
    if (n % p !== 0) continue;
    out.push(p);
    while (n % p === 0) n /= p;
  }
  if (n > 1) out.push(n);
  return out;
}
const factors = primeFactors(modulus);
assert.equal(factors.length, 1, "An odd prime power is required");
const [p] = factors;
const totient = modulus - modulus / p;
function modPow(a, exponent, modulus) {
  const q = BigInt(modulus);
  let current = BigInt(a) % q;
  let out = 1n;
  for (let e = exponent; e > 0; e = Math.floor(e / 2)) {
    if (e % 2) out = out * current % q;
    current = current * current % q;
  }
  return Number(out);
}
const divisors = primeFactors(p - 1);
let generator = 2;
// Choose the least positive integer primitive modulo every power of p.
while (divisors.some(d => modPow(generator, (p - 1) / d, p) === 1) ||
  modPow(generator, p - 1, p * p) === 1 || generator % p === 0) ++generator;
const powers = [1];
for (let k = 1; k < totient; ++k) powers.push(modPow(generator, k, modulus));
assert.equal(new Set(powers).size, totient);
assert.ok(powers.every(a => a % p !== 0));
assert.equal(modPow(generator, totient, modulus), 1);

function atanBounds(q) {
  let lo = 0n;
  let hi = 0n;
  for (let k = 0; k <= 24; ++k) {
    const exponent = BigInt(2 * k + 1);
    const d = exponent * q ** exponent;
    const a = scale / d;
    const b = ceilDiv(scale, d);
    lo += k % 2 ? -b : a;
    hi += k % 2 ? -a : b;
  }
  return [lo - ceilDiv(scale, 51n * q ** 51n), hi];
}
const a5 = atanBounds(5n);
const a239 = atanBounds(239n);
const piLo = 16n * a5[0] - 4n * a239[1];
const piHi = 16n * a5[1] - 4n * a239[0];
assert.ok(3n * scale < piLo && piLo <= piHi && piHi < 4n * scale);

const factorial = [1n];
for (let k = 1; k <= 27; ++k) factorial[k] = factorial[k - 1] * BigInt(k);
function truncation(n, d, parity, last) {
  const degree = 2 * last + parity;
  let numerator = 0n;
  for (let k = 0; k <= last; ++k) {
    const j = 2 * k + parity;
    const term = n ** BigInt(j) * d ** BigInt(degree - j) *
      (factorial[degree] / factorial[j]);
    numerator += k % 2 ? -term : term;
  }
  return [numerator * scale, d ** BigInt(degree) * factorial[degree]];
}
const negate = ([lo, hi]) => [-hi, -lo];
function rootBounds(k) {
  const quadrant = Math.floor(4 * k / totient);
  const residue = BigInt(4 * k % totient);
  const denominator = 2n * BigInt(totient);
  const error = ceilDiv((piHi - piLo) * residue, denominator);
  const angle = piLo * residue;
  const bounds = parity => {
    const [lo, ld] = truncation(angle, denominator * scale, parity, 13);
    const [hi, hd] = truncation(angle, denominator * scale, parity, 12);
    return [floorDiv(lo, ld) - error, ceilDiv(hi, hd) + error];
  };
  const c = bounds(0);
  const s = bounds(1);
  return [[c, s], [negate(s), c], [negate(c), negate(s)], [s, negate(c)]][quadrant];
}
const roots = Array.from({ length: totient }, (_, k) => rootBounds(k));

function isqrt(n) {
  if (n === 0n) return 0n;
  let r = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
  for (;;) {
    const next = (r + n / r) / 2n;
    if (next >= r) return r;
    r = next;
  }
}
const weights = Array(modulus).fill(0n);
for (let n = 1; n <= terms; ++n) {
  if (n % p === 0) continue;
  weights[n % modulus] += isqrt(scale ** 2n / BigInt(n));
}
const tail = ceilDiv(BigInt(modulus) * scale ** 2n, 2n * isqrt(BigInt(terms)));
function component(k, axis) {
  let lo = -tail;
  let hi = tail;
  for (let i = 0; i < totient; ++i) {
    const w = weights[powers[i]];
    const upperWeight = w + BigInt(periods);
    const [a, b] = roots[k * i % totient][axis];
    lo += a * (a < 0n ? upperWeight : w);
    hi += b * (b < 0n ? w : upperWeight);
  }
  return [lo, hi];
}
const display = ([lo, hi]) => [
  Number(floorDiv(1000n * lo, scale ** 2n)), Number(ceilDiv(1000n * hi, scale ** 2n)),
];
const rows = [];
for (let k = 1; k < totient; ++k) {
  if (modulus !== p && k % p === 0) continue;
  const real = component(k, 0);
  const imaginary = component(k, 1);
  const excludesZero = ([lo, hi]) => lo > 0n || hi < 0n;
  rows.push({
    index: powers[k], dual: powers[totient - k], exponent: k, parity: k % 2,
    realThousandths: display(real), imaginaryThousandths: display(imaginary),
    centralOrderZero: [real, imaginary].some(excludesZero),
  });
}
rows.sort((a, b) => a.index - b.index);
console.log(JSON.stringify({ modulus, generator, terms, rows }));
