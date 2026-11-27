import assert from "node:assert/strict";

// Verify the finite arithmetic and interval estimates used for the central
// order of 389.a1. The analytic identities and the infinite-tail bounds are
// justified in ../LMFDB.md. This checker uses only integer arithmetic.

const conductor = 389;
const limit = 64;
const endpoint = 64;
const steps = 128;
const scale = 10n ** 20n;
const ceilDiv = (n, d) => (n + d - 1n) / d;
const mulLower = (a, b) => a * b / scale;
const mulUpper = (a, b) => ceilDiv(a * b, scale);
const mod = (n, p) => ((n % p) + p) % p;

function points(p) {
  const affine = [];
  for (let x = 0; x < p; ++x) {
    for (let y = 0; y < p; ++y) {
      if (mod(y * y + y - x * x * x - x * x + 2 * x, p) === 0) {
        affine.push([x, y]);
      }
    }
  }
  return [null, ...affine];
}

function add(p, left, right) {
  if (left === null) return right;
  if (right === null) return left;
  const [x, y] = left;
  const [u, v] = right;
  if (x === u && mod(y + v + 1, p) === 0) return null;
  const numerator = x === u ? 3 * x * x + 2 * x - 2 : v - y;
  const denominator = x === u ? 2 * y + 1 : u - x;
  const m = Array.from({ length: p }, (_, k) => k)
    .find(k => mod(k * denominator - numerator, p) === 0);
  assert.notEqual(m, undefined);
  const z = mod(m * m - 1 - x - u, p);
  return [z, mod(-1 - y - m * (z - x), p)];
}

const pointKey = point => point === null ? "O" : point.join(",");
const p5 = points(5);
const p11 = points(11);
const doubles = new Set(p11.map(point => pointKey(add(11, point, point))));
const P = [0, 0];
const Q = [1, 0];
const sumPQ = add(11, P, Q);
assert.equal(p5.length, 9);
assert.equal(p11.length, 16);
assert.deepEqual([...doubles].sort(), ["3,5", "6,4", "6,6", "O"]);
for (const point of [P, Q, sumPQ]) assert.ok(!doubles.has(pointKey(point)));

const coeff = [0n, 1n];
for (let n = 2; n <= limit; ++n) {
  const p = Array.from({ length: n - 1 }, (_, k) => k + 2).find(k => n % k === 0);
  let cofactor = n / p;
  let power = p;
  while (cofactor % p === 0) {
    cofactor /= p;
    power *= p;
  }
  if (n === p) coeff[n] = BigInt(p + 1 - points(p).length);
  else if (cofactor === 1) {
    coeff[n] = coeff[p] * coeff[n / p] - BigInt(p) * coeff[n / (p * p)];
  } else coeff[n] = coeff[power] * coeff[cofactor];
}
assert.equal(coeff[3], -2n);

// 157/50 < pi < 22/7 gives 318/1000 < 2*pi/sqrt(389) < 319/1000.
assert.ok(157n ** 2n * 1000n ** 2n > 318n ** 2n * 25n ** 2n * BigInt(conductor));
assert.ok(44n ** 2n * 1000n ** 2n < 319n ** 2n * 7n ** 2n * BigInt(conductor));

const factorial = [1n];
for (let j = 1; j <= 15; ++j) factorial[j] = factorial[j - 1] * BigInt(j);
function expTruncation(a, b, terms) {
  let numerator = 0n;
  for (let j = 0; j <= terms; ++j) {
    const term = (-a) ** BigInt(j) * b ** BigInt(terms - j);
    numerator += term * (factorial[terms] / factorial[j]);
  }
  assert.ok(numerator > 0n);
  return [numerator * scale, b ** BigInt(terms) * factorial[terms]];
}
function expNegBounds(divisor) {
  const [loN, loD] = expTruncation(319n, 1000n * BigInt(divisor), 15);
  const [hiN, hiD] = expTruncation(318n, 1000n * BigInt(divisor), 14);
  return [loN / loD, ceilDiv(hiN, hiD)];
}

function logRatio(n, d) {
  assert.ok(d <= n && n <= 2n * d);
  const numerator = (n - d) * scale;
  const denominator = n + d;
  const zLo = numerator / denominator;
  const zHi = ceilDiv(numerator, denominator);
  const squareLo = mulLower(zLo, zLo);
  const squareHi = mulUpper(zHi, zHi);
  let loPower = zLo;
  let hiPower = zHi;
  let lo = 0n;
  let hi = 0n;
  for (let k = 0; k < 16; ++k) {
    const divisor = BigInt(2 * k + 1);
    lo += 2n * loPower / divisor;
    hi += ceilDiv(2n * hiPower, divisor);
    loPower = mulLower(loPower, squareLo);
    hiPower = mulUpper(hiPower, squareHi);
  }
  // 2*sum_{k>=16} z^(2k+1)/(2k+1) <= 3/3^33 for 0 <= z <= 1/3.
  return [lo, hi + ceilDiv(3n * scale, 3n ** 33n)];
}
const [ln2Lo, ln2Hi] = logRatio(2n, 1n);
function logAt(gridPoint) {
  const n = BigInt(gridPoint);
  let d = BigInt(steps);
  let k = 0n;
  while (n >= 2n * d) {
    d *= 2n;
    ++k;
  }
  const [lo, hi] = logRatio(n, d);
  return [lo + k * ln2Lo, hi + k * ln2Hi];
}

let [qLo, qHi] = expNegBounds(1);
const [stepLo, stepHi] = expNegBounds(steps);
let [logLo] = logAt(steps);
let sum = 0n;
for (let i = steps; i < endpoint * steps; ++i) {
  const nextLo = mulLower(qLo, stepLo);
  const nextHi = mulUpper(qHi, stepHi);
  const [nextLogLo, nextLogHi] = logAt(i + 1);
  let lowerPower = scale;
  let upperPower = scale;
  let fLower = 0n;
  for (let n = 1; n <= limit; ++n) {
    lowerPower = mulLower(lowerPower, nextLo);
    upperPower = mulUpper(upperPower, qHi);
    fLower += coeff[n] * (coeff[n] < 0n ? upperPower : lowerPower);
  }
  const logBound = fLower < 0n ? nextLogHi : logLo;
  sum += fLower * logBound * logBound;
  qLo = nextLo;
  qHi = nextHi;
  logLo = nextLogLo;
}
const gridDenominator = BigInt(steps) * scale ** 3n;
assert.ok(1000n * sum >= 2341n * gridDenominator, "The finite integral lower bound must be at least 2341/1000");

// Independently check the rational coefficient and integration tails.
const firstOmitted = BigInt(limit + 1);
const x = BigInt(endpoint);
assert.ok(200n * 16000n * 3n ** firstOmitted < 27n * firstOmitted ** 2n * 4n ** firstOmitted);
assert.ok(200n * 32n * (90n * x * x + 600n * x + 2000n) * 3n ** x < 27n * 4n ** x);
console.log(JSON.stringify({
  groupOrder5: p5.length,
  doubles11: [...doubles].sort(),
  sumPQ11: sumPQ,
  a3: Number(coeff[3]),
  finiteIntegralLowerThousandths: Number(sum * 1000n / gridDenominator),
  coefficientTailLessThan: "1/200",
  integrationTailLessThan: "1/200",
}));
