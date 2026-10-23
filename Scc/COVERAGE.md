# scc coverage of WeakCore

Every WeakCore construct and what scc does with it.  Sources:
the surface syntax `WeakCore/Syntax.lean` (`pOp`, `pExpr`, `pTy`, `pDecl`,
`pProg`), the AST `WeakCore/CoreTerm.lean` (`Op`, `Expr`, `Decl`) and
`WeakCore/CoreLang.lean` (`Ty`), and the runtime meaning
`WeakCore/TermRun.lean` (`evalOp`, `tstep`).

**Status** is one of:

* **lowered**: accepted by the frontend and compiled (`Scc/Lower/Term.lean`).
* **rejected (rule)**: a deliberate fragment rule, kept on purpose.
* **rejected (deferred)**: left out on purpose until something else exists.
  The reason is given.
* **rejected (missing)**: no reason beyond the work; marked *cheap* when the
  lowering is a few IR instructions with no new IR or runtime support.
* **unreachable**: no checked program can reach the construct while the rest
  of the fragment stands.  The frontend still rejects it.

**Rejection site** gives the line of `Scc/Frontend.lean` that produces the
diagnostic: `tyBad` for types (block signatures, and the type arguments of
`newBuf`, `zero`, `pack`, calls and `spawn`), `opBad` for operations (reported
by `exprDiags` at line 350), and `exprDiags` for terms.  Line numbers are for
this revision.  A rejected operation's diagnostic reads
`<construct> is not in the accepted fragment (in 'f', binding 'x')`.

The table describes the fragment as it stands.  The object layout is about to
change (bipartite objects, two-word locatives, header words).  That change
alters what `new`, `fld`, `b[i]`, `newBuf`, the loads and stores and the
pointer types lower to, but not which constructs the frontend accepts.

## Declarations and programs

| Construct (surface) | AST | Status | Notes / rejection site |
|---|---|---|---|
| `def f(x : τ) : σ = e` | `Decl` | lowered | One IR function `wc_f`; arguments and results flattened, at most 32 argument words (past the registers on the stack) and six result words (`lowerDecl`). |
| index parameters `def f{i, …}` | `Decl.idx` | lowered | Erased. |
| type parameters `def f[α : κ, …]` | `Decl.tparams` | rejected (deferred) | Line 415.  Needs monomorphisation: a `tvar`'s layout is fixed only by the instantiation (`TermRun.accs (.tvar _) = none`). |
| `type N = τ` | parser `Env.addType` | lowered | Expanded by the parser. |
| `proto N = P` | parser `Env.addProto(2)` | lowered | Expanded by the parser.  Only protocol words use it, and those are rejected. |
| `main` | — | rule | `entryOf`, lines 379–399: `main` takes `Unit`, `Ptr pub Void` (its `ThreadId`) or `S * Ptr pub Void` with a setup block `rodata`, and returns `Int` (the exit status) or `Unit`. |
| block named `spawn` | — | rule | Line 190: reserved for the provisional spawn form. |
| externs `print`, `park`, `unpark` | `Decl` | lowered | Provisional: recognised by signature (`externOf`); the body is ignored. |

## Terms (`Expr`)

| Surface | AST | Status | Notes / rejection site |
|---|---|---|---|
| `let x = op` | `let_` | lowered | See the operations below. |
| `let (x, y) = a` | `split` | lowered | |
| `let <i, x> = unpack a` | `unpack` | lowered | Index erased. |
| `let <[α], x> = unpack a` | `unpackT` | lowered | Witness erased. |
| `if a = b then … else …` | `ifeq` | lowered | |
| `ret a` | `ret` | lowered | |
| `tail f(a)` | `tail` | lowered | A tail call, or a call and return for an extern. |
| `let <r, p, t> = region a` | `region` | rejected (missing, cheap) | Line 358.  At runtime it is `publish`'s release fence plus zero-width bindings. |
| `let <r, p, c> = openPub a` | `openPub` | rejected (missing, cheap) | Line 359.  No code: zero-width bindings. |
| `ifnull a then … else x => …` | `ifnull` | rejected (missing, cheap) | Line 361.  A compare with 0 (heap addresses are never 0). |
| `parity a of 2k => … \| 2k+1 => …` | `parity` | rejected (missing, cheap) | Line 362.  A test of the low bit. |
| `case a of inl x => … \| inr y => …` | `case` | rejected (deferred) | Line 360.  Needs WeakCore's sum layout tiers: niche (pointer tag bits), wide (a 16-byte granule, which must be loaded and stored single-copy atomically) and boxed (an allocation per injection, `injM`/`projM`). |
| `cas w e -> v as t then … else …` | `cas` | rejected (missing) | Line 363.  On a plain `pub` cell (CoreTerm `checkExpr` `.cas`) it needs a compare-and-swap instruction in the IR and both emitters (`lock cmpxchg`, `casal`).  On a protocol word it is deferred with protocol words. |
| `casp w (e0, e1) -> (v0, v1) as t then … else …` | `casp` | rejected (deferred) | Line 364.  Protocol pairs: a 16-byte compare-and-swap (`cmpxchg16b`, `casp`). |

## Operations (`Op`)

| Surface | AST | Status | Notes / rejection site |
|---|---|---|---|
| `a`, `()`, a literal | `atom` | lowered | A literal ≥ 2^64 is rejected (rule), lines 332–338. |
| `(a, b)` | `pair` | lowered | |
| `a + b` | `add` | lowered | Always checked: on a sum ≥ 2^64 the program takes the abort outcome (a departure from WeakCore's unbounded `Int`; see `Scc/Frontend.lean`). |
| `a - b` | `sub` | lowered | Saturating, which is exactly `TermRun.subW`. |
| `a mod n` | `rem` | rejected (missing, cheap) | Line 308.  The checker requires `n : Int[v+1]`, so `n > 0`: one `urem`. |
| `a & m` | `band` | rejected (missing, cheap) | Line 310.  One `and`. |
| `new a` | `new` | lowered | Bump allocation. |
| `null : Ptr? μ τ` | `null` | rejected (missing, cheap) | Line 299 (and `Ptr?` at line 273).  The word 0. |
| `fold a : τ` | `fold` | rejected (missing, cheap) | Line 300 (and `mu` at line 278).  No code. |
| `publish a` | `publish` | lowered | `fence st`. |
| `intoRgn r a` | `intoRgn` | rejected (missing, cheap) | Line 301.  `publish`'s fence. |
| `newBuf[τ] n` | `newBuf` | lowered | One-word elements only (line 267).  The arena is zeroed, so the slots are born zero. |
| `b[i]` | `idx` | lowered | |
| `bufInit b i v` | `bufInit` | lowered | A plain store to slot `i` (the checker's `ini`); the only way to fill a buffer of non-zeroable elements (`Ptr`, `Loc`). |
| `fld k a` | `fld` | lowered | |
| `load a`, `load acq a` | `load` | lowered | |
| `load b[i]` | `loadAt` | lowered | |
| `load b[i].p` | `loadAtF` | rejected (missing, cheap) | Line 311.  Needs arrays of multi-word elements (line 267), whose lowering already scales by the element's words. |
| `store a v`, `store rel a v` | `store … none` | lowered | |
| `store … with t` | `store … (some t)` | rejected (missing, cheap) | Line 289.  On a region cell it is a plain store (the token is zero-width).  On a protocol word it is deferred with protocol words. |
| `fence ld\|st\|full` | `fence` | lowered | |
| `mkWord r P v t` | `mkWord` | rejected (deferred) | Line 302.  Protocol words (§7 row 20): the type `Word` (line 276) with its tokens, `cas` and `fetch`. |
| `mkWord2 r P (v0, v1) t` | `mkWord2` | rejected (deferred) | Line 315.  Protocol pairs: 16-byte single-copy-atomic accesses. |
| `ldp [acq] a as (n0, n1)` | `ldp` | rejected (deferred) | Line 316.  As `mkWord2`. |
| `stp [rel] a (v0, v1) with t` | `stp` | rejected (deferred) | Line 317.  As `mkWord2`. |
| `mkEPair r P (v0, v1)` | `mkEPair` | rejected (deferred) | Line 318.  Epoch pairs: as `mkWord2`. |
| `mkTicket r N P v t` | `mkTicket` | rejected (deferred) | Line 319.  Two protocol words. |
| `claim a with t` | `claim` | rejected (deferred) | Line 320.  Zero-width, but only meaningful on protocol words. |
| `fetch op [acq] [rel] a v` | `fetch` | rejected (deferred) | Line 325.  On an `Int` cell, `fetch add` is unbounded: the checked form must be a CAS loop that aborts before storing on overflow, so it waits for `cas`.  `or`/`and`/`xor` need the same CAS loop on x64. |
| `pack a at i : τ` | `pack` | lowered | Erased. |
| `pack a at [σ] : τ` | `packT` | lowered | Erased. |
| `validate x` | `validate` | unreachable | Line 303.  The checker needs `x` to be a torn read, which only a load of a protocol word makes. |
| `f[τ…]{i…}(a)` | `call` | lowered | Type arguments are checked by `tyBad` (line 294).  A block with type parameters is rejected at its definition. |
| `borrow s t` | `borrow` | rejected (missing, cheap) | Line 304.  Zero-width. |
| `endBorrow t` | `endBorrow` | rejected (missing, cheap) | Line 305.  Zero-width. |
| `xchg a v` | `xchg` | lowered | A plain load then a plain store: the cell is held exclusively. |
| `fnptr f` | `fnptr` | rejected (missing) | Line 306.  Needs an indirect call in the IR and both emitters, plus stack maps at indirect call sites. |
| `callc f a` | `callc` | rejected (missing) | Line 307.  As `fnptr`.  It is also the only way to call the closures of WeakCore's libraries (`Fn(A, B)`, `ArrayLib`). |
| `nameI a` | `nameI` | lowered | No code. |
| `xchg b[i] v` | `xchgAt` | lowered | |
| `xchg b[i].p v` | `xchgAtF` | rejected (missing, cheap) | Line 312.  As `loadAtF`. |
| `bits op a b` | `bits` | lowered | All except `msb16`. |
| `bits msb16 a b` | `bits .msb16` | rejected (missing, cheap) | Line 296.  A pure function of two words (gather the top bit of each byte, about 30 IR instructions). |
| `bit1 op a` | `bit1` | lowered | |
| `vmatch lo hi b` | `vmatch` | rejected (missing, cheap) | Line 309.  Pure, as `msb16` (byte compares). |
| `zero[τ]` | `zero` | lowered | |
| `freeze t` | `freeze` | rejected (missing, cheap) | Line 313.  Zero-width. |
| `cvt U8…I64 a` | `cvt` | lowered | |
| `toInt a` | `toInt` | lowered | |
| `asLanes U8…I64 a` | `asLanes` | lowered | |
| `fop op a b` | `fop` | lowered | |
| `fcmp op a b` | `fcmp` | lowered | |
| `fop1 op a` | `fop1` | lowered | |
| `lane a j` | `lane` | lowered | |
| `setLane a j v` | `setLane` | lowered | |
| `ldl b i`, `stl b i v` | `ldl`/`stl` | rejected (missing, cheap) | Line 314.  One sub-word load or store at `b + i·w/8`.  The store goes to an own buffer, which the sub-word ownership hypothesis `SubWordOwned` (`Scc/Emit/X64Lowerable.lean`) already covers. |
| `ldlw b wi j`, `stlw b wi j v` | `ldlw`/`stlw` | rejected (missing, cheap) | Line 314.  As `ldl`/`stl`, at `b + 8·wi + (j mod 64/w)·w/8`. |
| `inl[τ] a`, `inr[τ] a` | `inl`/`inr` | rejected (deferred) | Line 298.  Sums: see `case`. |
| `spawn{f}(a)` | `spawn` | lowered | Provisional surface form (`rewriteSpawnE`).  Threads past `Layout.maxThreads` take the abort outcome. |

## Types (`Ty`)

Types are checked where `tyBad` sees them (see above).  A value of a rejected
type cannot arise inside a block without a rejected operation or signature.

| Surface | AST | Status | Notes / rejection site |
|---|---|---|---|
| `Unit`, `Void` | `unit`, `void` | lowered | Zero words. |
| `Int`, `Int[i]` | `int`, `intS` | lowered | One word. |
| `U8 … I64` | `fix` | lowered | The pattern, zero-extended. |
| `LanesU8 …` | `lanes` | lowered | One word. |
| `σ * τ` | `prod` | lowered | Concatenated words. |
| `σ + τ` | `sum` | rejected (deferred) | Line 271.  See `case`. |
| `Code(σ, τ)` (and the alias `Fn(σ, τ)`, which expands to a package holding one) | `code` | rejected (missing) | Line 272.  See `fnptr`/`callc`. |
| `Array[i] τ` | `array` | lowered for one-word `τ` | Line 267: multi-word or empty elements are rejected (missing, cheap; the lowering already scales by the element's words). |
| `Ptr own/pub τ`, `Loc own/pub τ` | `ptr`, `loc` | lowered | One word. |
| `Ptr[r] τ`, `Loc[r] τ` (region mode) | `ptr (.rgn r)` | rejected (missing, cheap) | Line 257.  The same word as `pub`. |
| `Ptr? μ τ` | `ptrOpt` | rejected (missing, cheap) | Line 273.  One word, 0 for null. |
| `Share[r]` | `share` | rejected (missing, cheap) | Line 274.  Zero-width. |
| `Cap[s, r]` | `cap` | rejected (missing, cheap) | Line 275.  Zero-width. |
| `Tok[r]` (plain region) | `tok r none` | rejected (missing, cheap) | Line 277.  Zero-width. |
| `Tok[r, P, i]` and the pair and epoch tokens | `tok r (some _)`, `tok2`, `tokE` | rejected (deferred) | Line 277.  Protocol words. |
| `Word[r, P]` | `word` | rejected (deferred) | Line 276.  Protocol words. |
| `Pair[r, P]`, `EPair[r, P]` | `word2`, `epair` | rejected (deferred) | Line 276.  16-byte granules. |
| `mu a. τ` | `mu` | rejected (missing, cheap) | Line 278.  The layout of the unrolling (`TermRun.accs`). |
| `forall a. τ` | `iall` | unreachable | Line 279.  No checker rule introduces or eliminates a value of type `∀a. τ`, so only a parameter could hold one, and no caller could pass it. |
| `exists a. τ` | `iex` | lowered | Erased; a two-word coupled package is a 16-byte granule and has no layout (`Frontend.words`). |
| `exists (α : κ). τ` | `tex` | lowered | As `iex`. |
| `{ν : τ \| ψ}` | `refine` | lowered | Erased. |
| type variable | `tvar` | lowered under `tex` | A block's own type parameters are rejected (see `Decl.tparams`). |

## Departures and checks beyond WeakCore

* `Int` `+` aborts on a sum ≥ 2^64 (exit status 101); WeakCore's `Int` is
  unbounded.
* Literals must fit in 64 bits.
* Resource limits are abort outcomes that the source semantics does not have:
  heap, stack (per-thread cap and pool) and threads (`Layout.maxThreads`).
