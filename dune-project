(lang dune 3.0)
(name proofsystemzoo)
(version 0.3.0)
(generate_opam_files true)
(package
 (name proofsystemzoo)
 (synopsis "A zoo of propositional proof systems over one local benchmark database")
 (description
  "Eleven propositional proof systems (truth tables, the Resolution family, DRAT, Nullstellensatz, Polynomial Calculus, PCR, Cutting Planes, Sherali-Adams, Sum-of-Squares) sharing one SQLite benchmark store, with independent verifiers, exact certificates and a parallel runner.")
 (authors "Zunchen Huang")
 (license MIT)
 (depends
  (ocaml (>= 4.14))
  dune
  zarith
  sqlite3
  yojson))
