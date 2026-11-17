# proofsystemzoo

A zoo of propositional proof systems over one local benchmark database,
written in OCaml.

Eleven proof systems run on the same benchmarks, kept in one SQLite file.
They range from truth tables and Resolution to Nullstellensatz, Polynomial
Calculus, Cutting Planes, Sherali–Adams and Sum-of-Squares. Every system has
a proof search and an independent verifier, and the runner trusts neither:

- every reported proof has passed the verifier;
- every reported lower bound comes with a certificate that has been checked;
- every "satisfiable" comes with an assignment that was checked against the
  original benchmark.

Answers are exact. Floating point steers some searches, but anything that
becomes a proof or a certificate is checked in integer, GF(p) or rational
arithmetic.

```
$ proofsystemzoo init
$ proofsystemzoo run --jobs 4
195 jobs in 9.7s (4 parallel): 128 refuted, 23 satisfiable, 18 limit, 0 timeout, 26 n/a, 0 problems
$ proofsystemzoo report
benchmark             expect  TT     tree  ord   res   DRAT  NS2  NS3  PC2  PC3  PCR2  PCR3  CP    SOS    DSOS   SA
--------------------  ------  -----  ----  ----  ----  ----  ---  ---  ---  ---  ----  ----  ----  -----  -----  ---
parity-3              UNSAT   n/a    n/a   n/a   n/a   n/a   n/a  n/a  n/a  n/a  n/a   n/a   4     n/a    n/a    3*
parity-5              UNSAT   n/a    n/a   n/a   n/a   n/a   n/a  n/a  n/a  n/a  n/a   n/a   4     n/a    n/a    4*
php-2-1               UNSAT   4      5     5     5     1     2*   2*   2    2    2     2     4     2      2      1
php-3-2               UNSAT   64     21    20    20    2     4*   4*   3    3    3     3     12    2      4      2*
php-3-3               SAT     sat*   sat*  sat*  sat*  sat*  sat  sat  sat  sat  ≥7    ≥7    sat*  limit  limit  ≥6*
php-4-3               UNSAT   4096   85    68    68    7     6*   6*   4    4    4     4     35    4      limit  3*
php-5-4               UNSAT   limit  377   247   247   28    ≥6*  ≥6*  5    5    ≥4    ≥4    70    limit  limit  ≥4*
tseitin-cycle-4       UNSAT   16     15    15    15    2     2*   3*   2    2    2     2     17    2      4      2*
tseitin-cycle-6       UNSAT   64     23    23    23    2     2*   3*   2    2    2     2     25    2      4      2*
tseitin-cycle-6-even  SAT     sat*   sat*  sat*  sat*  sat*  sat  sat  sat  sat  sat   sat   sat*  limit  limit  sat
tseitin-grid-2x3      UNSAT   128    39    35    35    4     3*   4*   3    3    3     3     41    4      4      3*
tseitin-cycle-8       UNSAT   256    31    31    31    2     2*   3*   2    2    2     2     33    2      4      2*
tseitin-grid-3x3      UNSAT   4096   179   103   103   16    4*   6*   4    4    4     4     149   4      limit  ≥4*
```

Each cell shows the system's measure (size or degree) of its best proof:

| cell | meaning |
|---|---|
| `6*` | a minimum: a checked lower-bound certificate proves no smaller proof exists |
| `≥6*` | a budget ran out, but 6 is certified |
| `≥4` | a budget ran out at 4, not certified |
| `sat*` | satisfiable, and the witness was checked |
| `n/a` | no encoding reaches the system's input language |
| `·` | not run |

## Build

The only requirements are OCaml ≥ 4.14, dune ≥ 3.0, zarith, sqlite3 and
yojson. Only the standard library is used beyond those (no Base or Core).

```bash
opam install dune zarith sqlite3 yojson
# or: apt install ocaml-nox ocaml-dune libzarith-ocaml-dev libsqlite3-ocaml-dev libyojson-ocaml-dev
dune build          # _build/default/bin/main.exe
dune test           # about 38,000 checks in about 15 s
dune install        # puts proofsystemzoo on your PATH
```

## Usage

The database is `$PROOFSYSTEMZOO_DB`, or `~/.proofsystemzoo/zoo.db`;
`--db PATH` overrides both.

```bash
proofsystemzoo init                          # create and seed with the 13-benchmark starter suite
proofsystemzoo gen php n=5                   # PHP with 6 pigeons, 5 holes
proofsystemzoo gen tseitin graph=grid size=4x4
proofsystemzoo add my.cnf --expected UNSAT   # .cnf (DIMACS), .poly, .opb/.ineq
proofsystemzoo list
proofsystemzoo zoo                           # the systems, by group

proofsystemzoo run --jobs 4                  # every default instance on every benchmark
proofsystemzoo run --systems 'nullstellensatz[p=5],sum-of-squares[cone=sos]' --family php \
                   --timeout 120 --limit max_size=600000
proofsystemzoo report --format md            # text, md or csv

proofsystemzoo show php-4-3                  # details and runs (--payload for the instance)
proofsystemzoo proof php-4-3 drat            # the stored proof, as JSON
proofsystemzoo certificate php-4-3 'nullstellensatz[p=2]'
proofsystemzoo check php-4-3 drat proof.drat           # verify an external proof (JSON or DRAT text)
proofsystemzoo check-cert php-4-3 sherali-adams cert.json
proofsystemzoo audit                         # re-verify every stored proof and certificate
```

A system is named with optional parameters, for example
`nullstellensatz[p=3]` or `sum-of-squares[cone=dsos]`. A run is cached:
with the same system version and configuration it is not repeated, unless
you pass `--force`. Each job runs in its own process under a hard timeout
(default 30 s). The search gets 90% of the timeout as its time budget.

## The systems

| system | group | reads | measure | search | lower-bound certificate | Krajíček |
|---|---|---|---|---|---|---|
| `truth-table` | logical | cnf | size | all 2ⁿ assignments | — | |
| `tree-resolution` | logical | cnf | size | DPLL with pruning | — | §5 |
| `ordered-resolution` | logical | cnf | size | Davis–Putnam elimination | — | §5 |
| `resolution` | logical | cnf | size | minimum-width saturation, then Davis–Putnam and DPLL; smallest proof kept | — | §5 |
| `drat` | logical | cnf | size | CDCL; learnt clauses are RUP lemmas | — | |
| `nullstellensatz[p]` | algebraic | poly ← cnf-poly | degree | exact minimum degree over GF(p) | design: L(1) = 1, L(m·fᵢ) = 0 | §6.2 |
| `polynomial-calculus[p]` | algebraic | poly ← cnf-poly | degree | exact minimum degree (degree-d closure) | — | §6.2 |
| `pcr[p]` | algebraic | poly ← cnf-poly-twin | degree | as PC, with twin variables x̄ = 1 − x | — | §6.2 |
| `cutting-planes` | geometric | ineq ← cnf-ineq | size | gcd rounding, clique cuts, exact LP; resolution simulation | — | §6.3 |
| `sum-of-squares[cone]` | semialgebraic | poly ← cnf-poly | degree | `sos`: SDP + exact rounding; `dsos`: exact LP | — | §6.4 |
| `sherali-adams` | semialgebraic | ineq ← cnf-ineq | degree | exact minimum degree via exact LP | point: a pseudo-expectation | §6.4 |

The default instances run NS, PC and PCR at p = 2 and p = 3, and SoS with
both cones; any prime p < 2³⁰ works. "Exact minimum degree" means the
search tries degrees in increasing order and decides each one exactly.

- NS and Sherali–Adams also emit a certificate that the degree they moved
  past has no proof: a design or a point. The runner checks it, and that
  is what puts the `*` on a minimum.
- PC and PCR decide each degree exactly too, but they have no certificate
  format for it, so their minima carry no `*`.
- Sherali–Adams decides a degree only when the LP's answer can be
  certified. Otherwise it moves on without a certificate.

## Benchmarks

The families are `php` (pigeonhole), `tseitin` and `parity`:

- `php m=.. n=..` is PHPᵐₙ.
- `tseitin graph=cycle|grid|complete size=..` is a Tseitin formula. Add
  `odd=false` for a satisfiable control.
- `parity n=..` is 2·Σxᵢ = 2⌊n/2⌋+1, an integer program with no 0/1
  solution.

Instances are kept as canonical text. Their identity is
`language:sha256(text without comments)`, so generating an instance again,
or adding the same formula from a file, finds the stored one.

There are three input languages: CNF in DIMACS, polynomial equations, and
linear inequalities in OPB style.

```
p 2 3                    * #variable= 2 #constraint= 3
c var 1 p0_0             * var 1 p0_0
1 -1*x1 = 0              +1 x1 >= 1 ;
1 -1*x2 = 0              +1 x2 >= 1 ;
1*x1*x2 = 0              -1 x1 -1 x2 >= -1 ;
```

The encodings `cnf-poly` (a clause becomes the indicator of its falsifying
assignments), `cnf-poly-twin` (for PCR) and `cnf-ineq` translate CNF for
the algebraic and geometric systems.

## Proofs and certificates

Proofs are JSON objects with a `format` tag. The formats are stable, so
other tools can produce them and check them (`check`), and consume them (for
instance a formalised checker kept as a separate add-on).

| format | content |
|---|---|
| `truth-table/1` | `falsified`: one clause index per assignment |
| `resolution-dag/1` | `lines`: `{c, rule: axiom}` or `{c, rule: res, from: [i, j], pivot}`; optional `order` (ordered resolution) |
| `drat/1` | `steps`: `["a", lits]` / `["d", lits]`; DRAT text is accepted too |
| `ns/2` | `p`, `terms`: `{ax, mult: [[vars, c], …]}` with Σ gᵢ·fᵢ = 1 over GF(p) |
| `pc/1` | `p`, `lines`: `axiom` / `mul` (x · line) / `lin` (Σ c · line); last line a non-zero constant |
| `cp/1` | `lines`: `axiom` / `bound` / `add` / `div`; last line 0 ≥ b > 0 |
| `sa/1` | `terms`: `{ax, S, T, coef}`, Σ coef · ∏ₛx ∏ₜ(1−x) · (aᵢx − bᵢ) = negative constant |
| `sos/1` | `squares`: `{c, s}`, `ideal`: `{ax, mult}`, Σ c·s² + Σ hᵢfᵢ = −1 over ℚ |

Certificates are `{"witness": {"assignment": {"1": true, …}}}` and
`{"lower_bound": …}`. A lower bound is either an NS design
(`{"metric": "degree", "value", "p", "design"}`) or an SA point
(`{"metric": "degree", "value", "point"}`).

## How it is built

### Types

- **Languages are a GADT.** A value of type `a Lang.t` witnesses that
  instances of that language have OCaml type `a`. `Lang.equal` returns a
  type equality, and encodings are typed by two witnesses.
  `Encodings.convert : 'b Lang.t -> problem -> ('b * …, string) result`
  returns exactly the type the caller asked for. A system therefore only
  ever sees its own input type.
- **Systems are modules.** `System.S` has abstract types `config`, `input`,
  `proof` and `lower_bound`, with a JSON codec for each, and a verifier
  `config -> input -> proof -> (Measures.t, string) result`. A system
  without lower-bound certificates uses the empty type `Nothing.t`, whose
  checker is the empty match. Instances are first-class modules carrying
  their parsed configuration.
- **Functors are applied at run time.** `nullstellensatz[p=5]` builds
  `Field.Gf (struct let p = 5 end)` when it is configured. Each instance
  picks its monomial representation (`Mono.Word` or `Mono.Big`). The
  algorithms are functors over both: `Ring.Make (K) (M)`,
  `Echelon.Make (R)`. Elements of different fields, or monomials of
  different representations, cannot be mixed.
- **Canonical objects are private types.** Clauses, CNFs, polynomials and
  ring elements can only be built by their modules, which sort and
  normalise them.
- **Everything returns a `result`.** Decoders and verifiers report errors as
  values. The only exception that crosses module boundaries is
  `Clock.Timeout`, raised when a budget runs out. The runner relies on this
  when it decodes a child's outcome with the system's own codecs before
  verifying it.

### Algorithms

- **Monomials.** A monomial over up to 56 variables is one immediate
  integer: a bitmask with the degree in the top bits. Integer comparison is
  then a graded order, a product is an `lor` plus a popcount, and beyond 56
  variables Zarith bitsets take over. Polynomials are sorted parallel
  arrays, so addition and multiplication by a variable are single merges.
- **Echelon bases with reduction traces.** Each basis vector remembers how
  it was reduced. One back-substitution then expresses a target in terms of
  the generators (the NS certificate). Polynomial Calculus derivations are
  read straight off the traces. The PC closure is incremental across
  degrees, and NS designs come out of the same basis.
- **Linear programming.** A floating-point revised simplex does the search.
  It uses a product-form inverse with periodic reinversion, a crash basis,
  a feasibility-preserving perturbation, devex pricing, a Harris ratio test
  and a Bland fallback. Its answers are rounded to rationals and checked
  exactly, with exact fallbacks behind them. Cutting Planes certificates
  are also economised: expensive rows (clique cuts) are excluded while the
  system stays infeasible, and then the support is made irreducible.
- **Semidefinite programming.** Douglas–Rachford splitting alternates two
  projections: onto the affine coefficient equations (one Cholesky
  factorisation of AAᵀ) and onto the PSD cone (Householder plus QL
  eigendecomposition). The numerical Gram matrix is then made exact:
  1. Add the Gram matrix of Σ χ_S², where χ_S = ∏(1 − 2xᵢ). Since χ_S² = 1
     on the cube, this matrix represents a constant and is positive
     definite, which gives a guaranteed margin.
  2. Round, coarsest precision first.
  3. Project exactly onto the coefficient equations.
  4. Decompose into squares with an exact LDLᵀ.
- **Runner.** Each job runs in its own forked child under a hard timeout.
  The outcome comes back as JSON, is decoded with the system's codecs and
  is judged by the parent. `--jobs N` runs N children at once.

## Performance

On the starter suite, all 16 default instances on all 13 benchmarks make
195 jobs. With default limits on a 2-core machine they take 18.3 s
sequentially and 9.7 s with `--jobs 4`. Some single runs, all including
verification:

| run | time |
|---|---|
| Sherali–Adams, php-4-3 (certified minimum 3) | 0.09 s |
| Sherali–Adams, php-5-4 (certifies ≥ 4) | 3.6 s |
| DSOS, php-4-3 (decides degree 4) | 0.12 s |
| SoS, php-4-3 (degree 4) | 1.3 s |
| SoS, tseitin-grid-3x3 (degree 4) | 3.9 s |
| Nullstellensatz, php-5-4 with `--limit max_size=600000` (certifies ≥ 8) | 0.8 s |

## Budgets

| system | `max_size` counts | default |
|---|---|---|
| truth-table | variables (`max_vars`) | 18 |
| tree-resolution | proof lines | 300 000 |
| ordered-resolution | clauses | 300 000 |
| resolution | clauses per width bound | 200 000 |
| drat | conflicts | 200 000 |
| nullstellensatz | generators | 60 000 |
| polynomial-calculus, pcr | lines | 200 000 |
| cutting-planes | clique variables (`max_vars`) | 64 |
| sherali-adams | LP columns (products) | 50 000 |
| sum-of-squares `dsos` | LP columns | 60 000 |
| sum-of-squares `sos` | Gram basis size | 120 |

The other limit keys are `time`, `max_degree`, `max_width` and `max_vars`,
for example `--limit max_degree=6`. `PSZ_DEBUG=1` prints the progress of
the LP and SDP solvers.

## Extending

- **A system** is a module of type `System.S`: metadata, parameters,
  `configure`, `search`, `verify`, codecs and optionally
  `check_lower_bound`. Add it to `Registry.builtin`, or call
  `Registry.register` from your own executable. A system whose `searches`
  returns false is verifier-only.
- **A family** is a generator in `families.ml`. **An encoding** is a value
  of type `(src, dst) Encodings.t`. **A language** is a new constructor of
  `Lang.t` with its text format.

Krajíček's chapters 6 and 7 suggest where the zoo can grow, and which
existing pieces each addition would reuse:

| section | candidates | would reuse |
|---|---|---|
| 6.2 | NS / PC over ℚ (`Field.Rational`), other monomial orders | `Ring`, `Echelon` |
| 6.3 | stabbing planes, CP with bounded coefficients | `Lp`, the `cp/1` checker |
| 6.4 | Lovász–Schrijver (LS, LS₊), Positivstellensatz calculus | `Lp`, `Sdp`, exact rounding |
| 7.1 | Res(k), R(LIN), Res(CP): clauses of linear forms | the resolution checker, `cnf-ineq` |
| 7.2 | Frege and circuit Frege | a formula language (`Lang.t`) and a rule checker |
| 7.5 | the Ideal Proof System | algebraic circuits, randomised identity testing |

## Tests

`dune test` runs three suites:

- **algebra**: monomials (word against bitset), field laws, polynomial
  arithmetic checked by evaluation on the cube, echelon express and design,
  LP answers (certificates, points, exact solutions), the SDP and dense
  kernels, codecs, and stable content hashes.
- **systems**: 120 random formulas through all 16 instances. It checks
  soundness, completeness on unsatisfiable formulas, checked lower bounds,
  PC ≤ NS and PCR ≤ PC in degree, and resolution sizes. It also checks that
  every encoding preserves satisfying assignments, and that every verifier
  rejects tampered proofs.
- **e2e**: a fresh database and the full matrix in parallel. It compares
  the report with the expected matrix, then checks caching, the audit, an
  external DRAT text proof, a corrupted proof and a stored certificate.

## Layout

```
lib/core      json codecs, measures, limits, clock, parameters, sha256, helpers
lib/lang      clauses, CNF, polynomials, inequalities; the language GADT; encodings; families
lib/algebra   fields, monomials, polynomial rings, echelon bases, LP, dense algebra, SDP
lib/systems   the System.S contract, the eleven systems, the registry
lib/store     the SQLite store
lib/run       the parallel runner (judging, audit, external checks) and reports
bin/main.ml   command-line interface
test/         the test suites
```

## License

MIT
