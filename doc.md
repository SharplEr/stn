# Semantic Types Notation (STN)

Status: draft specification, version 0.1.

This document formalizes STN for parser and validator authors. **Confirmed**
decisions incorporate the author's clarifications. **Proposed** conventions
supply concrete details absent from the initial description. **Open** issues
are explicitly identified rather than silently resolved.

## 1. Purpose

STN describes the semantic structure of a program or library: its types,
available computations, and required features. It supplements a natural-language
specification with a structure that can be checked for missing computation paths.

A document contains two sections:

~~~stn
DEFINITIONS:
// Semantic types, traits, and available functions.

FEATURES:
// Required computations.
~~~

A type denotes a meaning, not a physical representation or a particular value.
Different values may share a semantic type. Different semantic types may share
a representation, and different occurrences of one semantic type may use
different representations.

The notation does not specify algorithms, storage layouts, implementation
classes, inheritance, scheduling, or a particular programming language.
Validation establishes derivability from the stated contracts. It does not
verify an implementation or interpret prose as executable constraints.

For example, a string hash and a string length should have different types:

~~~stn
DEFINITIONS:
/// A hash of a string.
Hash
/// The length of a string.
Size
hash: String -> Hash
length: String -> Size

FEATURES:
stringSize: String -> Size
~~~

The validator preserves these distinctions, but cannot determine from prose
whether two uses of a type mistakenly represent different meanings.

## 2. Source format and comments

The following concrete lexical conventions are **proposed** for version 1:

- Source is UTF-8. LF and CRLF line endings are accepted.
- Identifiers match [A-Za-z_][A-Za-z0-9_]* and are case-sensitive.
- Type-name capitalization is a convention, not a syntactic requirement.
- DEFINITIONS, FEATURES, exists, and from are reserved words.
- Punctuation tokens are colon, equals, pipe, arrow, dot, angle brackets,
  comma, and parentheses.
- The two sections occur exactly once, in the order shown above.
- Top-level declarations have zero indentation. Trait members use a positive,
  consistent indentation prefix, using spaces or tabs. Mixing spaces and tabs
  within a prefix or changing the prefix within a trait is rejected. This
  convention accepts the tab-indented members in validator.stypes.
- Each declaration occupies one physical line, except a trait and its members.
  Multiline type expressions are outside this first grammar.
- Blank lines and ordinary comment-only lines do not affect indentation.

An ordinary comment starts with `//` and extends to the end of the line.
It does not contribute to the declared semantics.

A semantic description starts with `///` at the beginning of a line, after
optional indentation. It belongs to the next declaration at that indentation
level. Consecutive description lines form one description; intervening blank
lines and ordinary comments are ignored. An unattached description is an error.
Inline semantic descriptions are not supported by the proposed grammar.

Recognize `///` before `//`. Preserve descriptions and source locations in
the AST. A description is part of the contract, even though the proof engine
does not reason about its natural-language contents.

## 3. Concrete grammar

This EBNF uses lexer tokens NEWLINE, INDENT, DEDENT, DOC_LINE, and identifier.
Blank lines and ordinary comments have already been removed from the token
stream. Quoted angle brackets are literal syntax.

~~~ebnf
document          = "DEFINITIONS", ":", NEWLINE,
                    { definition },
                    "FEATURES", ":", NEWLINE,
                    { feature } ;

descriptions      = { DOC_LINE, NEWLINE } ;
definition        = descriptions,
                    ( type-declaration | trait-declaration | function-declaration ) ;

type-declaration  = identifier, [ parameters ],
                    [ "=", type-expression ], NEWLINE ;
trait-declaration = identifier, [ parameters ], ":", NEWLINE,
                    INDENT, member, { member }, DEDENT ;
member            = descriptions, identifier, [ parameters ], ":",
                    type-expression, [ "->", type-expression ], NEWLINE ;

function-declaration = qualified-name, [ parameters ], ":",
                       type-expression, "->", type-expression, NEWLINE ;
feature           = descriptions, qualified-name, [ parameters ], ":",
                    type-expression, "->", type-expression, NEWLINE ;

parameters        = "<", binder, { ",", binder }, ">" ;
binder            = identifier, "from", type-expression ;

type-expression   = primary, { "|", primary } ;
primary           = type-reference | parenthesized | existential ;
type-reference    = identifier, [ "<", type-expression,
                                    { ",", type-expression }, ">" ] ;
parenthesized     = "(", ")"
                  | "(", type-expression, ")"
                  | "(", type-expression, ",", type-expression,
                         { ",", type-expression }, ")" ;
existential       = "exists", binder, ":", type-expression ;
qualified-name    = identifier, { ".", identifier } ;
~~~

An existential body extends to the end of its enclosing type expression.
Consequently, `exists T from S: F<T> | None` puts None inside the body;
`(exists T from S: F<T>) | None` puts it outside.

Parentheses around one type are grouping. A comma makes a product:
`(Bar | Baz, Size)` has two components. `()` is the empty product.
Trailing commas and singleton-product syntax are not supported.

A declaration with a colon followed by NEWLINE starts a trait. A colon followed
by a type expression starts a function or member signature. Only trait members
may omit the arrow and input type.

**Proposed:** finite parameters are allowed on opaque types and defined types,
as well as on traits and functions. This makes families used in the examples
explicitly declarable:

~~~stn
ColumnName<T from ColumnType>
Column<T from ColumnType>
~~~

Neither the use of an undeclared name nor an applied name implicitly declares
a type family.

## 4. Type model

### 4.1 Opaque types and singleton markers

~~~stn
/// The ordinal of a document within its segment.
DocId
/// A marker indicating that no documents remain.
NO_DOCS
~~~

Each bare declaration introduces a distinct nominal type. The representation
and cardinality of an ordinary opaque type are unspecified.

Singleton markers such as NO_DOCS, ASC, and DESC use the same syntax.
Their singleton meaning comes from the declared contract. The grammar does
not distinguish them mechanically from opaque types such as DocId.
For type checking and proof search, all these names are atomic types.

A type is not a value. The fact that a marker has one value does not make other
values of a semantic type identical.

### 4.2 Built-ins

Built-in names cannot be redeclared.

| Type | Meaning |
| --- | --- |
| Boolean | The two Boolean values. |
| Int8, Int16, Int32, Int64 | Signed integers of width n: -2^(n-1) through 2^(n-1)-1. |
| UInt8, UInt16, UInt32, UInt64 | Unsigned integers of width n: 0 through 2^n-1. |
| Byte | Exactly eight opaque bits, without a signed arithmetic interpretation. |
| Float32, Float64 | Floating-point values with the indicated contract width. |
| None | A singleton type with the sole value None, representing absence. |
| String | A string, without a prescribed encoding or physical representation. |
| Bytes | A predefined type whose structural description is List<Byte>. |
| List<T> | A finite sequence; order and repetitions matter. |
| Set<T> | A finite set. |
| Map<K, V> | A finite partial mapping from K to V. |

Byte, UInt8, and Int8 are different types. No implicit numeric conversion,
widening, or shared-representation conversion is provided.

None is different from `()`. Absence and successful completion without
returned components have different meanings, despite both having one value.

**Proposed:** Bytes follows the ordinary nominal-definition rule and is not
a transparent alias. It has the same structural view as List<Byte>, but its
nominal identity is preserved.

**Open, without affecting parser or proof search:** specify whether Float32
and Float64 require the complete IEEE 754 binary32/binary64 domains, including
NaNs and infinities. Width alone does not specify those details.

### 4.3 Nominal definitions

~~~stn
MatchedDocs = Set<DocId>
TopDoc = (DocId, SegmentId, Score)
Order = ASC | DESC
~~~

The equals sign introduces a new nominal type with a structural description,
not a transparent alias. If `A = Set<DocId>` and `B = Set<DocId>`, A, B,
and the anonymous Set<DocId> are distinct types.

Two separate operations are required in a validator:

1. **Identity:** compare nominal names, applied nominal families, and normalized
   anonymous type expressions.
2. **Shape inspection:** inspect a nominal declaration's structural description
   when applying a specified structural rule.

Shape inspection does not replace nominal identity throughout the type system.
An arbitrary Set<DocId> is not automatically a MatchedDocs value.

**Confirmed:** structural inference may produce a nominal collection result.
For example, with `Scores = Set<Score>` and `score: DocId -> Score`,
mapping may prove `MatchedDocs -> Scores`.

**Confirmed:** structural conversion is directed: MatchedDocs may be viewed as
Set<DocId>, but an arbitrary Set<DocId> cannot automatically become MatchedDocs.
No nominal constructor is implicitly available. Identity preserves the exact
input type, including its nominal name. Section 7.7 specifies a separate lifting
rule for transformations between nominal collections; it is not view conversion
followed by an implicit constructor.

### 4.4 Products

A product is an ordered tuple. Its components may be any types.

~~~stn
TopDoc = (DocId, SegmentId, Score)
Foo = (Bar | Baz, Size)
~~~

**Proposed:** product shape is exact. `(A, (B, C))` and `(A, B, C)` are
different types. Order, multiplicity, and nesting are significant; grouping
parentheses around a single type are not.

Product reassociation, permutation, distribution over sums, and flattening
are not type-equality rules. Receiver insertion for trait methods is a specified
syntax transformation, not a general product equivalence.

### 4.5 Sums and normalization

Anonymous sums are associative, commutative, and idempotent:

~~~text
A | B       = B | A
(A | B) | C = A | (B | C)
A | A       = A
~~~

Normalize a sum by recursively normalizing its operands, flattening anonymous
sum nodes, removing identical operands, and sorting by a stable structural key.
A singleton sum normalizes to its sole operand. There is no empty-sum syntax.

Do not unfold nominal definitions during equality normalization.
If `S = A | B`, the expression `S | C` has the nominal alternative S
and the alternative C; it is not identical to `A | B | C`.

To inspect a sum's alternatives for a finite domain, inspect the outer
structural description. If `S = A | B | C`, `T from S` ranges over A,
B, and C. If `R = S | D`, `T from R` ranges over S and D, not A, B,
C, and D.

**Proposed:** a nonsum type used as a domain has one alternative: itself.
This permits a singleton finite domain.

### 4.6 Collections

List, Set, and Map have arities one, one, and two respectively. Their arguments
are types, not runtime values.

The notation does not prescribe hashing, sorting, iteration order for sets or
maps, contains performance, or data layout. Semantic equality is presupposed
for set elements and map keys; its implementation is outside STN.

Mapping a set may merge equal results. Map-value mapping preserves keys and
their associations. There is no general implicit covariance:
List<A> is not automatically List<A | B>.

### 4.7 Finite parameters

~~~stn
ColumnType = Int64 | Blob | Keywords | FloatVector

findColumn<T from ColumnType>: (Table, ColumnName<T>) -> Column<T> | None
~~~

A declaration parameter denotes a finite set of static specializations.
Substitute each permitted type consistently for every bound occurrence.
Multiple parameters expand over the Cartesian product of their domains.

Each type family application must have the declared arity, and each argument
must belong to its parameter's finite domain. Using a family name without its
required arguments does not imply an existential or an inferred argument.

**Proposed name-resolution rules:**

- Collect declarations before resolving references; forward references are allowed.
- Declaration parameters are scoped over their entire declaration.
- Trait parameters are also scoped over member signatures.
- Member parameters extend that scope without shadowing existing binders.
- Existential binders are scoped to their bodies and use capture-avoiding substitution.
- Parameter domains must be closed: they cannot depend on another parameter.
- Reject cycles in structural descriptions and domain dependencies in version 1.

Opaque nominal types can reference themselves in function signatures without
creating a structural-definition cycle. For example, a method returning its
receiver type is allowed.

Expansion is independent of the implementation language. An implementation
without generics may generate separate concrete functions or structures.

### 4.8 Existentials

~~~stn
AnyColumn = exists T from ColumnType: Column<T>
findColumn: (Table, String) -> AnyColumn | None
~~~

An existential value packages one runtime-selected witness type from the
finite domain and a value of the specialized body. Its static type does not
reveal which witness was selected.

An existential binder does not expand the containing function into overloads.
Declaration parameters are static choices; existential witnesses are dynamic
choices.

**Proposed:** normalize existentials up to bound-variable renaming, but do not
equate them with ordinary sums. No implicit packing, unpacking, dispatch, or
existential-elimination rule is supplied. Declare any required operation
explicitly in DEFINITIONS.

## 5. Functions and traits

### 5.1 Primitive functions

~~~stn
/// Computes the total size of all segments.
sum: SegmentSizes -> TotalSize
~~~

A function declares one available primitive morphism from its input type to its
output type. Multiple arguments and results use products.

Qualified names such as Info.create are function names; qualification alone
does not introduce a receiver.

Errors are output alternatives:

~~~stn
write: (FileWriter, Bytes) -> () | IOError
~~~

Whether an implementation uses returned variants or exceptions is outside the
notation. Error alternatives do not disappear during validation.

### 5.2 Traits and receiver insertion

~~~stn
FileWriter:
    append: Bytes -> () | IOError
    append: ByteIterator -> () | IOError
    rewrite: (FileOffset, Bytes) -> () | IOError
    fsync: () -> () | IOError
    length: () -> Size | IOError
~~~

A trait introduces a nominal receiver type and a group of primitive functions.
For receiver R, lower `m: I -> O` to
`R.m: receiverInput(R, I) -> O`, where:

~~~text
receiverInput(R, ())           = R
receiverInput(R, (A1, ..., An)) = (R, A1, ..., An)
receiverInput(R, A)            = (R, A) otherwise
~~~

Only the outermost anonymous argument product is flattened. A nominal type with
a product description remains one argument.

The example therefore lowers to:

~~~stn
FileWriter.append: (FileWriter, Bytes) -> () | IOError
FileWriter.append: (FileWriter, ByteIterator) -> () | IOError
FileWriter.rewrite: (FileWriter, FileOffset, Bytes) -> () | IOError
FileWriter.fsync: FileWriter -> () | IOError
FileWriter.length: FileWriter -> Size | IOError
~~~

A member `size: Size` abbreviates `size: () -> Size`.
In trait Info, it lowers to `Info.size: Info -> Size`.

An external declaration `Info.create: Size -> Info` is unchanged and can
describe a constructor or static operation.

Traits do not specify implementations, inheritance, structural subtyping,
or mandatory interfaces. One trait may become one concrete class or record.

### 5.3 Generic traits

~~~stn
FieldIterator<T from FieldValue>:
    value: T
    advance: DocId -> DocId | NO_DOCS
    nextDoc: () -> DocId | NO_DOCS
~~~

For each permitted V, instantiate the receiver as FieldIterator<V>, then
substitute V into all members and insert the receiver. For example:

~~~text
FieldIterator<V>.value: FieldIterator<V> -> V
FieldIterator<V>.advance: (FieldIterator<V>, DocId) -> DocId | NO_DOCS
~~~

These specialized qualified names are internal proof labels; their applied
receiver spelling does not extend the source grammar for qualified names.

## 6. Applicability, overloading, and features

### 6.1 Overloads

Overloads are permitted, but ambiguity is checked after all finite expansion
and trait desugaring. Two different names with identical signatures are allowed
and may yield different proofs.

**Confirmed:** reject overlapping applicable overloads instead of choosing a
more specific one. For example, the same name with inputs A and A | B is invalid:
a call with input A could use both. Return types do not resolve ambiguity.

**Proposed exact applicability model:** an input I is accepted by an input
contract D when I equals D, or when every alternative of I belongs to the
alternatives of an anonymous sum D. Nominal types, including named sums, remain
atoms for call applicability. Inspecting a named sum for a parameter domain or
collection narrowing does not make it an anonymous sum argument. Products are matched
component by component, with exact arity and nesting. No collection coercion
or arbitrary nominal conversion participates in applicability.

To detect overlap, test whether two inputs admit any common input:

- Equal atoms overlap.
- An anonymous sum overlaps another input if one of its alternatives overlaps that input.
- Two products overlap if they have the same arity and every component pair overlaps.
- Collection applications, existential packages, and opaque families require
  identity unless they occur as alternatives of an outer sum.
- Distinct nominal types are disjoint for this test, including named sums.

Treat these as syntactic semantic domains; equal physical representations do
not establish overlap. Reject expansion overlaps even when outputs coincide.
Report both source locations and the specializations responsible.

This proposed model also specifies sum-input restriction: a function accepting
A | B may be used on A. It supplies no scalar narrowing of a returned sum.
Section 7.6 records this adaptation explicitly as a proof rule rather than
silently changing primitive signatures.

### 6.2 Features

~~~stn
FEATURES:
searchTop: (TableReader, Query) -> TopDocs
~~~

A feature declares a goal, not a primitive morphism. A parameterized feature
expands into one goal per permitted substitution and succeeds only if all
specializations succeed.

Features never enter the available-function environment, including after they
are proved. A reusable computation must be declared in DEFINITIONS.

**Proposed:** feature names are unique in a separate namespace. A feature and a
primitive may have the same name; the primitive is usable solely because of
its declaration in DEFINITIONS.

## 7. Proof rules

Type matching below uses nominal identity and normalized anonymous expressions
unless a rule explicitly requests structural inspection. Every rule application
is recorded in the proof.

### 7.1 Identity and projections

**Confirmed:** include identity and product projections.

~~~text
id[A]: A -> A

project[i]: (A1, ..., An) -> Ai    for 1 <= i <= n
~~~

Identity handles a goal whose result is already its input.
Projections make individual components of a feature's input available.
Each projection extracts one component; nested access uses multiple projections.

**Proposed:** projections may inspect a named product, for example
`TopDoc -> DocId`, without exposing any construction of TopDoc from an arbitrary
tuple. There is no projection from an empty product.

### 7.2 Composition

~~~text
f: A -> B      g: B -> C
-----------------------
g ∘ f: A -> C
~~~

The intermediate type must match. A sum containing an error does not match its
successful alternative by identity alone. Section 7.2.1 defines an explicit sum
extension rule that preserves unhandled alternatives, including errors.

#### 7.2.1 Sum extension and error propagation

Let sourceVariants(S) be the alternatives of S available to branch over:
flatten an anonymous sum, inspect the direct description of a nominal sum, and
treat any other type as a singleton. Keep a nominal sum S itself as the input
type; inspection does not replace its identity.

Let handled(A) be the alternatives explicitly accepted by f's input type A:
flatten an anonymous sum, but treat a nominal sum as one nominal alternative.
Require handled(A) to be a subset of sourceVariants(S). Let R be the sum of
sourceVariants(S) outside handled(A). If R is empty, omit it from the result.

~~~text
f: A -> C       handled(A) ⊆ sourceVariants(S)
------------------------------------------
extendSum[S,A](f): S -> C | R
~~~

This extends f to S: apply f to the A alternatives and pass every alternative
in R through unchanged. The input and output sums are normalized as usual.
For an explicitly defined nominal sum S, the extended function still accepts S;
inspection of its shape does not make S equal to its anonymous expansion.

For example:

~~~text
f: A -> C | D
-------------------------
extendSum[A | B,A](f): A | B -> C | D | B
~~~

This rule preserves alternatives; it does not discard them or classify them as
errors. It composes an operation that handles one branch with a later operation
while carrying the other branches forward unchanged.

Thus, if `tryB: A -> B | Error` and `useB: B -> C`, extend useB over the
input sum `B | Error` to obtain `B | Error -> C | Error`. Compose that
extension with tryB to prove `A -> C | Error`. The error branch remains in
the result. This does not prove `A -> C`, because that goal would discard the
Error outcome.

Each sum extension is one inference-rule application in a proof. The rule can
be used at an intermediate step; it is not restricted to the feature boundary.

### 7.3 Collection mapping

~~~text
f: A -> B
----------------------------
mapList(f): List<A> -> List<B>

f: A -> B
-------------------------
mapSet(f): Set<A> -> Set<B>

f: A -> B
-------------------------------------
mapValues(f): Map<K, A> -> Map<K, B>
~~~

The informal name map covers both mapList and mapSet. Map values are
transformed without changing keys.

If `f: A -> B | Error`, mapping a list produces List<B | Error>.
It does not produce List<B> | Error.

### 7.4 List flat mapping

~~~text
f: A -> List<B>
--------------------------------
flatMap(f): List<A> -> List<B>
~~~

Apply f to elements and concatenate its results in input order. No set or
map flat-mapping rule is included.

### 7.5 Collection narrowing

For an anonymous sum, variants(X) is its normalized set of alternatives.
For a nonsum atom, it is the singleton set containing that atom.
Named sum inspection uses the outer structural description, not representation
or recursive expansion of nominal alternatives.

~~~text
variants(U) ⊆ variants(S)
--------------------------------
narrowList[S, U]: List<S> -> List<U>

variants(U) ⊆ variants(S)
-----------------------------
narrowSet[S, U]: Set<S> -> Set<U>

variants(U) ⊆ variants(S)
----------------------------------
narrowKeys[S, U]: Map<S, V> -> Map<U, V>
~~~

Narrowing filters by type alternative. Lists retain relative order and
multiplicity; sets retain membership; maps retain the values of retained keys.
Implementations must be able to recognize alternatives at runtime.

The subset may be equal for anonymous types, although identity is simpler.
There is no empty target sum and no scalar narrowing `B | Error -> B`.
No predicate filter or mapKeys rule is included.

### 7.6 Fanout and sum-input restriction

~~~text
f: A -> B      g: A -> C
-------------------------
f &&& g: A -> (B, C)
~~~

Fanout requires both results from one logical input. It does not mandate two
independent calls, a copying operation, or a particular evaluation order.
Implementation may coordinate operations over mutable state.

This rule produces a binary product. Repeating it produces nested products;
there is no implicit flattening into an arbitrary flat tuple.

The following additional rule is **proposed** to make the overload applicability
model in Section 6.1 available to proof search:

~~~text
f: D -> O      accepts(D, I)
--------------------------
restrictInput[I](f): I -> O
~~~

For equal I and D, use f directly. For other cases, record a restriction node.
This rule admits a narrower sum input into a function accepting a wider input.
It does not remove output errors and does not convert unrelated nominal types.

### 7.7 Directed views and nominal structural lifting

**Confirmed example:**

~~~stn
MatchedDocs = Set<DocId>
Scores = Set<Score>
score: DocId -> Score
~~~

The validator must be able to prove MatchedDocs -> Scores through mapping.
That is a structural inference, not an identity or a general alias conversion.

For every nominal type N with an instantiated structural description E, a
directed view is available:

~~~text
view[N]: N -> E
~~~

There is no reverse view. This rule also applies to the proposed nominal Bytes
built-in. Named sum/product descriptions are exposed only through a directed
view or an explicitly specified inspection rule, never by type equality.

To preserve the confirmed nominal-to-nominal mapping example without introducing
a general constructor, use this **proposed precise lifting profile**:

1. Anonymous collection inputs use the ordinary rules, producing anonymous
   collection outputs only.
2. Nominal collection inputs may use their outer collection shapes and produce
   anonymous results under those rules.
3. A nominal collection input may produce a nominal collection output when
   both shapes match a map, flatMap, mapValues, or narrow instance and the
   normalized source and result collection shapes differ.
4. An unchanged collection shape may retain its original nominal type, but may
   not acquire a different nominal name.
5. A new nominal target for narrow requires strict variant-set reduction.
6. Element, key, and value comparison uses nominal type identity. Their internal
   definitions are not recursively erased.

Thus map(score) may prove MatchedDocs -> Scores because its input and output
are nominal collections and Set<DocId> changes to Set<Score>.
It may also prove MatchedDocs -> Set<Score>.
From an anonymous Set<DocId>, it proves Set<Score>, not Scores.
Map(identity) cannot construct MatchedDocs from Set<DocId> or rename an existing
nominal Set<DocId> wrapper.

For flatMap, inspect or explicitly view a nominal list result of the element
morphism as needed. The witness proof must retain any view step; it is not
a hidden equality. The same applies to any composition requiring a structural
description as an intermediate type.

Nominal lifting is one abstract inference node, not a decomposition into
viewing and constructing. This is essential: there is no globally available
constructor E -> N. A declared primitive that returns N can still establish
such a result explicitly.

Additional prose invariants are not proved by structural lifting. For example,
matching a List<Score> shape does not prove that it is sorted. Declare a
dedicated function when an invariant needs an explicit implementation obligation.

**Proposed:** nominal products can be inspected by projection, but the binary
fanout rule returns an anonymous product. Named product construction requires
a declared morphism until a separate construction rule is agreed.

### 7.8 Deliberate omissions

No other structural morphism is implicit. In particular, the core does not
include scalar error elimination, existential packing/elimination, mapKeys,
tuple permutation/reassociation, arbitrary nominal conversion, or an automatic
`A -> ()`.

Add a primitive to DEFINITIONS when a required transformation is not covered.
The validator is intended to remain simple rather than infer arbitrary algorithms.

## 8. Proof structure and minimum cost

A proof is a typed expression tree. Each node records:

- Primitive or rule identity.
- Input and output type IDs.
- Child proofs.
- Parameter substitutions and rule-specific arguments.
- Source locations of primitive declarations.

The simplicity metric is the lexicographic pair (u, r):

1. u: number of occurrences of user functions.
2. r: number of inference-rule applications.

Count occurrences, not distinct names. The metric measures proof simplicity,
not execution time or the number of independent runtime calls.

~~~text
cost(primitive)       = (1, 0)
cost(unaryRule(p))    = cost(p) + (0, 1)
cost(binaryRule(p,q)) = cost(p) + cost(q) + (0, 1)
cost(identity)       = (0, 1)
cost(projection)     = (0, 1)
cost(narrow)         = (0, 1)
cost(view)           = (0, 1)
~~~

**Proposed:** structural nominal matching within map/narrow is part of that
rule application and adds no extra cost. Traits count as user functions.
Finite specialization adds no rule cost. A restriction node adds (0, 1).

A DAG may share proof storage, but its cost is that of the unfolded tree.

For each feature specialization, return a minimum-cost proof and at most
maxAlternatives equal-cost alternatives. maxAlternatives is a positive integer.
Do not include higher-cost proofs merely to fill the limit.

**Proposed:** alternatives are structurally distinct proof trees, deduplicated
by primitive identities, rule kinds, substitutions, types, and children.
Composition associativity and other categorical equations do not identify
different trees. Use a stable ordering when truncating alternatives.

Two paths ending in D establish the same semantic output type, not equality
of values, effects, or implementations. STN does not require diagrams to commute.

## 9. Finite proof search

### 9.1 Bound on synthesized intermediate types

**Confirmed:** search must limit the nesting depth of automatically synthesized
intermediate collections and products. Users should explicitly introduce complex
entities needed by their design.

Finite generic expansion alone does not bound proof search: map can repeatedly
wrap types, and fanout can repeatedly create products.

The following bound is **proposed**:

~~~text
depth(nominal type or ground nominal family application) = 0
depth(())                      = 0
depth(A | B | ...)              = max(depth(A), depth(B), ...)
depth(List<A>)                 = 1 + depth(A)
depth(Set<A>)                  = 1 + depth(A)
depth(Map<K,V>)                = 1 + max(depth(K), depth(V))
depth((A1,...,An))              = 1 + max(depth(A1),...,depth(An))
~~~

Existential packages are only taken from explicit declarations and expressions;
the search does not synthesize new existential binders. They may be interned as
fixed atomic nodes for this depth calculation.

Nominal names remain atoms for this bound. Their explicit structural
descriptions are still available for inspection. This lets a user name a complex
entity rather than require the solver to invent its shape.

All ground expressions explicitly present in the specification and their
subexpressions are admitted, even when they exceed the synthesis bound.
New anonymous intermediate types must have depth at most maxIntermediateDepth.

Depth alone does not bound tuple width. Also bound synthesized tuple arity by
maxTupleArity. **Proposed default:** the largest arity appearing after trait
desugaring, with a minimum of two. All explicitly present tuples are admitted.

**Proposed default:** maxIntermediateDepth is two. Both limits are validator
configuration, must be reported with results, and can be increased deliberately.
No particular default was stipulated by the original design.

### 9.2 Constructing the finite universe

Let U contain:

1. All ground expressions in expanded primitive and feature signatures.
2. All ground instantiated structural descriptions and their subexpressions.
3. The receiver-input products introduced by trait lowering.
4. All normalized anonymous types constructible from the finite set of ground
   nominal atoms and fixed existential packages, within the depth and arity bounds.

For existential bodies, collect their permitted witness-specialized ground
types without adding packing or unpacking morphisms.

Use only the built-in anonymous constructors: sums, products, List, Set, and Map.
All nominal family applications come from the declared finite domains.
Anonymous sums are sets of distinct alternatives; they do not create additional
nesting merely by reassociation or duplicates. This yields a finite U.

Constructing every member eagerly may be expensive. A validator may use lazy
generation, indexing, and goal-directed pruning, provided an exhaustive failure
still accounts for every admitted type and rule instance. If a separate resource
limit prevents that, report incomplete search instead of underivability.

Adding a type to U makes it searchable; it does not declare a primitive,
establish inhabitance, or grant nominal construction.

### 9.2.1 Implemented search profiles

The Rust validator provides two explicit universe profiles. They share the same
semantic type model and inference rules; they differ in which intermediate types
are admitted. This is an additional search bound, separate from nesting depth.

The default **relevant** profile starts with items 1–3 above and closes existing
collection contexts and sums under elementary transformations. It admits
explicit products without enumerating every possible product or collection
context. Ground shapes of all finite family specializations are included.
See README.md for the exact construction and configuration.

A proof returned in this profile is a valid language derivation. Its minimum
cost is certified in the relevant universe only. Exhaustive failure in that
universe is reported as UNRESOLVABLE_IN_RELEVANT_UNIVERSE; it does not assert
failure in the larger universe of Section 9.2. Naming an intermediate shape can
extend the relevant universe.

The **exhaustive** profile (`--exhaustive`) enumerates item 4 as well. Its atoms
include all declared ground nominal types, explicitly mentioned built-in scalar
types, fixed existential packages, and `()`. Unmentioned built-ins are excluded.
It uses the largest explicit tuple arity after trait lowering, with a minimum
of two. It can certify UNRESOLVABLE_WITHIN_BOUNDS on exhaustion of the relation.

Both profiles have type-count and work budgets. Hitting either reports
SEARCH_INCOMPLETE, without certifying a minimum or underivability. The Rust
implementation additionally limits a finite parameter environment to 100000
specializations; exceeding this guard is EXPANSION_LIMIT, a resource outcome.

### 9.3 Saturation algorithm

Intern types to stable IDs. For every pair (A, B) in U × U, maintain the best
known cost and up to maxAlternatives proof trees for A -> B.

Seed the relation with:

- Expanded primitives from DEFINITIONS.
- Identity, product projections, directed nominal views, and admitted sum
  extensions.
- Admitted narrowing instances.
- Any input-restriction instances specified by the chosen applicability model.

Then apply the rule instances whose types belong to U:

~~~text
repeat
    extend each eligible function over unhandled sum alternatives
    compose A -> B with B -> C
    lift A -> B through List, Set, and Map values
    flatMap A -> List<B> into List<A> -> List<B>
    fan out A -> B and A -> C into A -> (B, C)
    apply permitted nominal structural matching
    apply admitted input restrictions

    replace a pair's entry when a candidate has lower cost
    merge distinct proofs on equal cost, then truncate deterministically
until no entry changes
~~~

A work queue or weighted hypergraph avoids rescanning all pairs. Keep source
primitive declarations separately from the truncated proof relation.

Termination follows from a finite universe, nonnegative integer costs,
positive rule costs, and a finite number of retained alternatives.
The fixed point gives the minimum cost for every admitted derivable pair.
Alternative truncation does not enumerate all globally possible proofs.

The validator should independently check every emitted proof tree: matching
types, substitutions, subset premises, allowed nominal lifting, and total cost.

### 9.4 Meaning of failure

A failed exhaustive search means no derivation **within the configured bounds**.
It is not a claim that no unbounded derivation exists. Suggest naming an
intermediate type or increasing the bound when relevant.

Distinguish these statuses:

| Status | Meaning |
| --- | --- |
| INVALID_SPECIFICATION | Parsing, naming, type, domain, or overload validation failed. |
| PROVED | At least one checked minimum-cost proof was found. |
| UNRESOLVABLE_WITHIN_BOUNDS | Exhaustive bounded search found no proof. |
| SEARCH_INCOMPLETE | A resource limit prevented exhaustive search or certification of minimum cost. |

A valid witness found before completion may be reported as a witness, but not
as certified minimum cost unless the algorithm has established optimality.

## 10. Validation pipeline and diagnostics

Perform these phases in order:

1. Lex and parse, preserving descriptions and source spans.
2. Register built-ins and declaration names. A trait declares its receiver type;
   a separate type declaration of that name is a duplicate.
3. Resolve names, check constructor arity, parameter scope and domains, reject
   forbidden cycles, and normalize anonymous types.
4. Expand finite declarations and lower traits to primitive signatures.
5. Reject overlapping overloads, including those caused by expansion.
6. Construct the bounded type universe and search from DEFINITIONS only.
7. Check and return proofs, or issue detailed diagnostics.

Type names are unique. **Proposed:** type and function names occupy separate
namespaces; repeated function names are permitted only as valid overload sets.

A diagnostic should include a stable code, source location, declaration or
feature name, and the relevant normalized types. Important cases include:

- Unknown type or family.
- Duplicate type or reserved built-in declaration.
- Wrong constructor/family arity.
- Unbound parameter or argument outside its finite domain.
- Forbidden cyclic structural description.
- Overload intersection, with both locations and a witness input.
- Feature failure, including the specialization and search bounds.

For an unresolved goal, show useful reachable types and near matches:
unhandled output errors, missing nominal construction, incompatible tuple
shape, or an excluded intermediate type. Missing signatures are suggestions,
not uniquely required architectural repairs.

## 11. Examples

### 11.1 Composition

~~~stn
DEFINITIONS:
A
B
C
D
ab: A -> B
bd: B -> D
ac: A -> C
cd: C -> D

FEATURES:
result: A -> D
~~~

Both bd ∘ ab and cd ∘ ac have minimum cost (2, 1).
Adding `ad: A -> D` gives the cheaper proof ad with cost (1, 0).

### 11.2 Individual inputs, projections, and fanout

~~~stn
DEFINITIONS:
Source
Query
Hash
Size
hash: Source -> Hash
querySize: Query -> Size

FEATURES:
summary: (Source, Query) -> (Hash, Size)
~~~

A proof is `(hash ∘ project[1]) &&& (querySize ∘ project[2])`.
Its cost is (2, 5): two projections, two compositions, and one fanout.

For `unchanged: Source -> Source`, the proof is id[Source] with cost (0, 1).

### 11.3 Mapping and collection narrowing

~~~stn
DEFINITIONS:
Raw
Parsed
ParseError
parse: Raw -> Parsed | ParseError

FEATURES:
validItems: List<Raw> -> List<Parsed>
~~~

A proof is
`narrowList[Parsed | ParseError, Parsed] ∘ mapList(parse)`.
Its cost is (1, 3): mapping, narrowing, and composition.

This discards failed parses. Type derivability alone does not determine whether
discarding errors satisfies the feature's prose contract.

### 11.4 Scalar errors remain visible

~~~stn
DEFINITIONS:
A
B
C
Error
tryB: A -> B | Error
useB: B -> C

FEATURES:
resultWithError: A -> C | Error
successfulResultOnly: A -> C
~~~

The feature `resultWithError` is provable by extending useB over
`B | Error` and composing it with tryB. The proof has cost (2, 2): two user
functions, one sum extension, and one composition.

The feature `successfulResultOnly: A -> C` is not provable from these
declarations. The Error branch is preserved by sum extension; to remove it,
declare an explicit error-handling morphism.

### 11.5 Features are never available functions

~~~stn
DEFINITIONS:
A
B
C
ab: A -> B

FEATURES:
first: A -> B
missing: B -> C
second: A -> C
~~~

Only first is proved. Declaring missing does not provide a B -> C primitive,
and proving first does not add any new primitive.

### 11.6 Overlap after finite expansion

~~~stn
DEFINITIONS:
A
B
X
Y
Choices = A | B
f<T from Choices>: T -> X
f: A | B -> Y

FEATURES:
~~~

Reject the document. The specialization f<A> and the last declaration both
accept A. Their different output types do not resolve the ambiguity.

## 12. Remaining decisions

The author's clarifications confirm identity, projections, structural nominal
mapping such as MatchedDocs -> Scores, rejection of intersecting overloads,
directed nominal views without implicit constructors, error-preserving sum
extension, and a depth bound on synthesized intermediates.

Before freezing a fully normative version, settle or adopt the proposed
conventions for:

1. The precise nominal lifting profile in Section 7.7: anonymous inputs cannot
   produce nominal outputs, and identity cannot rename nominal types.
2. Sum-input restriction and component-wise applicability; named sums retain
   nominal identity during call matching.
3. Nominal product construction beyond projection and anonymous fanout.
4. The exact depth/arity conventions and default search limits.
5. Lexical syntax, forward references, parameter scopes, and exclusion of recursion.
6. Built-in Bytes nominality and the precise floating-point value domains.
7. Structural proof-tree alternatives and costs of the added structural rules.

Implementations must record their chosen profile. They must not import implicit
conversions or equality from their implementation language to fill these gaps.
