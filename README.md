# Semantic Types Notation validator

A Rust library and command-line validator for the language in [doc.md](doc.md).
It parses `.stypes` files, checks declarations and overloads, and constructs
checked proof trees for features. The semantic structure follows
[validator.stypes](validator.stypes); filesystem handling and command-line
configuration are concrete Rust code.

## Build and run

Rust 1.85 or newer is required. The CLI uses `clap` with its derive API to
declare arguments, validate numeric bounds, and generate help and version output.

```sh
cargo build --release
cargo run -- examples/search.stypes
cargo run -- validator.stypes
cargo run -- examples/validator-complete.stypes -o proofs.txt
cargo test
cargo clippy --all-targets -- -D warnings
```

The executable is `target/release/stn-validator`. Use `--help` to list options.
For example:

```sh
stn-validator design.stypes --max-depth 2 --max-proofs 3
stn-validator design.stypes --exhaustive --max-depth 0 --max-types 20000
```

| Option | Default | Meaning |
| --- | --- | --- |
| `--output PATH`, `-o PATH` | stdout | Destination for the report. |
| `--max-depth N` | 2 | Nesting bound for synthesized collections and products. Explicit shapes and their subexpressions are always admitted. |
| `--max-proofs N` | 5 | Maximum distinct normalized alternatives at minimum cost per feature. Must be positive. |
| `--max-types N` | 20000 | Resource limit on the type universe. Must be positive. |
| `--max-steps N` | 2000000 | Work budget shared by universe construction and proof search. Must be positive. |
| `--exhaustive` | off | Enumerate the complete bounded constructor universe described below. |

Exit codes: **0** all goals proved; **1** I/O failure; **2** invalid arguments,
syntax or specification; **3** a goal is unresolved in the selected universe;
**4** a resource limit prevented completion. A declarations-only file is valid.

## Reading proofs

The report header includes resource consumption, for example:

```text
budget-used: types=42 (0.21%), steps=14291 (0.71%)
```

Percentages use the configured `--max-types` and `--max-steps` limits. These
counters cover the entire shared search, including universe construction and
rule preparation, and survive an interrupted run. Types count occupied universe
capacity without duplicates; collecting an oversized explicit batch reports a
full type cap. Extra interned nodes and virtual normalization boundaries do not
consume that capacity. Steps count successfully charged work units; an attempt
after exhaustion does not increment the counter. With no features, search is
skipped and both counters are zero. The library exposes them as
`ValidationReport::usage` (`SearchUsage`).

Proved features are displayed as compositions of functions, with costs on a
separate line. Short expressions fit on one line:

```text
  cost: functions=3, rules=3
  run = Args.parse >>> extend(Args.run) >>> finish
```

Long pipelines put each outer step on its own line:

```text
  validate =
      Args.parse
      >>> extend(Args.loadInput)
      >>> extend(validateSource)
      >>> extend(ValidationReport.format)
```

`f >>> g` runs `f` followed by `g`. `f &&& g` obtains both results from the
same logical input; it does not require independent calls on a mutable object.
Mixed operators and nested fanouts use explicit parentheses, for example
`h >>> (f &&& g)` and `(f &&& g) &&& h`. Composition chains are flattened;
fanout grouping is preserved because it determines the product's structure.

`extend(f)` applies `f` to the sum alternatives it handles and carries the
other alternatives through unchanged. Its scope stays explicit:
`extend(f >>> g)` is not unconditionally interchangeable with
`extend(f) >>> extend(g)`; a later step might handle a carried alternative.
Collection lifts use `mapList(f)`, `mapSet(f)`, `mapValues(f)`, and `flatMap(f)`.
Structural steps remain visible as `id`, `view`, `project[1]` (one-based),
`narrowList`, `narrowSet`, `narrowKeys`, and `restrictInput(f)`.

Expressions omit type annotations, parameter substitutions, and declaration
locations. Feature specialization names and failure diagnostics retain types
where they identify the goal. Full typed witnesses and source metadata remain
available through the library API and are used by the independent checker.
The display is a readable summary, not a serialization of the typed evidence.

Search retains one original witness per normalized composition. Composition
associations and safe placements of `extend` share an alternative slot. An
extension can move across a pipeline only when every later step leaves its
carried variants untouched. Primitive specializations, operation order, fanout
grouping, projections, and collection operations remain significant. The exact
normalization procedure is defined in `doc.md` §8.1.

The renderer also groups identical displayed definitions and costs: omitting
types can make distinct normalized alternatives look alike. The `PROVED` count
refers to retained representatives, and multiple displayed entries show how
many representatives they contain. Each representative remains an original
checked proof with its original cost.

## Search scope

The default **relevant universe** starts with all ground declaration shapes,
specialized signatures, and their subexpressions. It closes existing collection
contexts and sums under elementary transformations: primitives, views,
projections, primitive input restrictions, mapping, flat mapping, collection
narrowing, and error-preserving sum extensions. Compatible nominal collection
results are retained as candidates. New anonymous shapes obey `--max-depth`.
Products are taken from explicit shapes and signatures; this profile does not
invent every possible tuple or collection context.

Within that fixed universe, the search applies **all** inference rules from
`doc.md`, including composition of derived proofs, ordered binary fanout,
restriction of derived inputs, and extension of derived morphisms over sums.
Every reported witness is checked independently against the declarations.

Minimum cost is certified **within the selected universe**. A failure in the
default profile is `UNRESOLVABLE_IN_RELEVANT_UNIVERSE`, not a claim about the
complete depth-bounded grammar. Naming a missing intermediate shape can extend
this universe. Use `--exhaustive` for the larger search described in §9.2 of
`doc.md`.

The **exhaustive universe** additionally contains `()`, every nonempty normalized
sum of ground atoms, and all combinations of anonymous List, Set, Map and
products within the depth bound. Tuple arity is bounded by the largest explicit
arity after trait lowering, with a minimum of two. Nominal family applications
are drawn from the declared finite domains, including unused families. Only
built-in scalar types mentioned in the specification are included as atoms.
Existential bodies contribute witness-specialized ground types without implicit
packing or elimination.

The number of anonymous sums is exponential. Even a small document can exhaust
the budget in exhaustive mode. A resource limit produces `SEARCH_INCOMPLETE`;
it never certifies failure or minimum cost. Exhaustive completion without a
witness produces `UNRESOLVABLE_WITHIN_BOUNDS`.

Finite elaboration has an additional guard of 100000 specializations per
parameter environment; exceeding it produces `EXPANSION_LIMIT` and exit code 4.
The proof alternative limit truncates normalized compositions deterministically
during search, so equivalent trees do not occupy separate slots. This remains a
bounded selection, not an enumeration of every distinct runtime implementation.

## Examples and the validator specification

[examples/search.stypes](examples/search.stypes) demonstrates nominal collection
mapping and preservation of a search error. Its minimum cost in the relevant
universe is `(2, 3)`.

The current `validator.stypes` parses and passes declaration validation, but its
feature is unresolved in the relevant universe. `findProofs` checks one feature;
there is no explicit operation which checks all features, retains configuration
and definitions, and constructs the keyed `Map` consumed by `formatProofs`.
The rules do not introduce keyed aggregation, distribute products over sums,
or construct arbitrary flat argument tuples.

[examples/validator-complete.stypes](examples/validator-complete.stypes) keeps
the current architecture explicit: command-line validation, input loading,
syntax parsing, semantic elaboration, shared proof search, report formatting,
output writing, and exit-status selection. `Args.loadInput`, `validateSource`, and
`Args.run` retain context and sequence the fallible stages. Unresolved and
incomplete searches become feature statuses in the report; library and I/O
failures propagate to the process boundary. Its `validate` and `run` features
are proved with costs `(4, 6)` and `(3, 3)` in the relevant universe.
These declarations express implementation obligations; the validator does not
execute the specified functions.

## Library and implementation

```rust
use stn_validator::{validate_source, ValidationOptions};

let source = String::from("DEFINITIONS:\nA\nFEATURES:\nsame: A -> A\n");
let report = validate_source("example.stypes", source, ValidationOptions::default()).unwrap();
assert!(!report.has_unresolved_features());
println!("{report}");
```

`ValidationOptions::max_proofs`, `max_types`, and `max_steps` use `NonZeroUsize`.
Clap rejects zero values during argument parsing, before opening the input file.
Library callers construct positive limits with `NonZeroUsize::new(value)`;
`max_depth` remains a `usize` because zero depth is valid.

`validate_source` consumes both the source buffer and `ValidationOptions`.
The options move through search into the returned report. Callers that reuse
the same configuration for several runs can explicitly clone it at the call site.

The public API exposes feature statuses, typed proof trees, costs and source
references. Proof search consumes the elaborated `Specification` and returns
one `SearchResult` owning its type store, compacted proof DAG, ground feature
signatures, outcomes, and search bounds. Its `into_report` method combines goals
with their outcomes, formats specialization names, and moves the stores into
the public report. `validate_source` orchestrates parsing, elaboration, search,
and report construction.

`ValidationReport::types` owns the shared `TypeStore`: type nodes,
the nominal declaration registry, and cached structural views. Nodes reference
their children through `TypeId`, and interning gives equal normalized types the
same identifier. Identifiers belong to one store; they cannot be compared across
independent validation runs. Use `report.types[id]` to inspect a node and
`report.types.display(id)` to format a type.

`ValidationReport::proofs` owns the `ProofStore`. Feature results contain
`ProofId` roots; inference children are identifiers in the same store.
Use `report.proofs[id]` to inspect a record and
`report.proofs.expression(id)` to format a witness as a single-line composition.
`ProofStore` owns verification. Search uses `check_against` with already resolved
declarations, checking rules, costs, primitive metadata, missing children, and
cycles without reparsing source. `ProofChecker` owns temporary traversal marks.
The external-witness helper `ProofStore::check` and its `ProofImporter` live
with their unit tests in `src/proof/tests.rs`, compiled only with `#[cfg(test)]`.
These tests translate identifiers into independent stores and deliberately edit
witnesses to check that invalid evidence is rejected.

`syntax::SourceText` takes ownership of one `String` without copying or scanning
its buffer; its constructor is infallible. `lines()` creates a lazy `SourceLines`
iterator with items of type `Result<SourceLine, ParseError>`. It skips ordinary
comments and blank lines, retains semantic descriptions, and returns borrowed
text and indentation slices with their original physical line numbers. The
iterator records skipped trailing lines too, so EOF diagnostics retain their
source positions. There is no line index or intermediate collection of lines.

`SourceText::parse` feeds this iterator into `DocumentParser` with a `for` loop.
Its automaton states are `ExpectDefinitions`, `Definitions`, `Trait`, and
`Features`. Trait state owns a `TraitBuilder`; on dedent it emits the completed
trait before the same line is accepted in Definitions state. `finish` closes an
active trait and checks pending descriptions and required sections at EOF.
Both preprocessing and parsing fail in source order, without scanning later
lines after an earlier error. Description slices are joined once when attached
to a declaration; the completed AST owns its strings and can outlive the buffer.

The CLI transfers its input buffer to `validate_source`. `SourceText` has no
source lifetime parameter. The source inspection helper `as_str` and the shorthand
parser used by tests live in `src/syntax/tests.rs` and are absent from the public
API. Elaboration consumes the parsed document and proceeds through registration,
cycle and body validation, morphism and feature expansion, and overload checks.
Function and feature names and descriptions move into one ground specialization;
additional specializations receive copies of this metadata. Proof traversal separates
endpoint checks, node contracts, and cost calculation; search handles interruptions
outside its successful result processing.

Both stores use `indexmap::IndexSet` to combine hash lookup with access by index,
keeping each node in a single collection. Inserting an equal node reuses its
index; appending a new node preserves all existing identifiers. Proof compaction
rebuilds the set and explicitly remaps the surviving roots and child references.

Type identifier sets also use `IndexSet` for hash lookup and deterministic
insertion-order iteration. Set equality is independent of insertion order.
Before rule indexing, the search universe is explicitly sorted by type structure.
`SearchUniverse` retains that sorted `IndexSet` for both indexed access and
reverse lookup, without rebuilding a vector and a separate lookup table.

Lookup-only tables and membership-only sets use `HashMap` and `HashSet`.
Traversed declaration and search collections use `IndexMap` and `IndexSet` for
reproducible iteration. Parameter environments and proof substitutions retain
`BTreeMap` for canonical name order in proof hashing and feature specialization names.

- `src/syntax.rs`: line lexer and recursive descent parser.
- `src/model.rs`: interned type graph and declaration registry, finite elaboration, trait lowering,
  cycle detection, existential normalization and overload intersection checks.
- `src/search.rs`: type-universe construction and an indexed weighted agenda.
- `src/proof.rs`: typed proof nodes, inference premises and witness checking.
- `src/proof/display.rs`: function-composition expressions and displayed alternatives.
- `src/proof/normalize.rs`: typed equivalence keys for alternative selection.
- `src/lib.rs`: validation API and report formatting.
- `src/main.rs`: declarative `clap` arguments and command execution through `Result`,
  with contextual errors handled once at the program boundary.

`search::run` coordinates universe construction, rule preparation, search, and
witness checking. `SearchUniverse` owns the fixed type ordering and local indices;
`RuleIndex` records input adaptations, collection lifts, and admitted fanout products.
`ProofSearch` owns the settled relation and its incoming/outgoing indices. Its
main loop settles a candidate, then delegates to separate methods for collection
lifts, input restriction, sum extension, composition, and fanout.

The agenda implements generalized Dijkstra search over morphism pairs. It borrows
the proof store and carries the remaining budget, so offering an inference handles
endpoint translation, cost calculation, deduplication, and budget accounting together.
Its `NormalForms` store interns typed composition keys and memoizes accepted
premises. These keys are temporary search state; the returned proof DAG contains
only original witnesses. Normalization reads the type store without interning
virtual intermediate sums or changing the search universe.
Unary rules and collection lifts are indexed by premise pairs; composition uses
incoming/outgoing indexes and fanout uses admitted product targets. Every parent
has greater lexicographic cost than either premise, so the first settled cost
for a pair is minimal. Equal-cost alternatives are bounded and deduplicated.
Proofs share premise identifiers in an interned DAG, but costs count occurrences
in the unfolded tree. Rejected candidates are not stored. Search stops after all
goal costs and their retained alternatives are settled, or after exhausting the
relation or work budget. Before returning the report, the proof store is compacted
to the reported roots and their reachable premises. The parser's existential AST
uses uniquely owned boxes; semantic types and proofs use indexed stores.

STN validates type-level derivability. Prose contracts, algorithms, value equality,
mutable-state coordination, and representation choices remain implementation
obligations.
