/-
**`WordsNone` at the load of any placed output** (x86-64): the invariant
`PrivInv` (`Spike/Lib/X64DmemPriv.lean`) at `loadProg` for every program the
`wideIn` check accepts and every entry stack clear of the layout, so along
every run from the load no thread loads a word of the heap or the static
image (`PrivKeys.wordsNone`). `placeOKAt` gives both premises (A4's
`wideIn_of_placeOKAt`; A1's `clear_link_of_placeOKAt`, or `Entry.Ok`).

- `wordsNone_load_of_wide`, `wordsNone_run_of_wide`: from `wideIn` and the
  entry's `clear`, at any well-formed layout;
- `wordsNone_stackMem`: the entry state's memory (`Entry.stackMem`, the
  loaded thread's) loads no heap or image word;
- `privInv_load_ofPlaceOKAt`: `PrivInv` at the load of a placed output, at
  any layout the entry is clear of;
- `wordsNone_load_ofPlaceOKAt`, `wordsNone_run_ofPlaceOKAt`: `WordsNone` of
  every thread at the load and along every run, at the link with the
  immediates `i` and an admissible entry `E` (`E.Ok`).
-/
import Spike.Lib.X64DmemPriv
import Scc.Cert.PlaceOKX64
import Scc.Sem.CorrectE

namespace Spike.Lib.X64DmemPriv

open Kraken Kraken.Promising Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64 Spike.Lib.DmemPriv

variable {n : Nat} {Λ : Scc.Sem.Layout} {E : Entry} {μ : Marks}

/-- **At load, no thread loads a heap or image word**, for a `wideIn`
program and an entry stack clear of the layout. -/
theorem wordsNone_load_of_wide {prog : List (Directive × Nat)} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hw : wideIn (prog.map (·.1)) = true) (hwf : Λ.WF) (hE : E.clear Λ = true) {tid : Nat} {t : Thread Kraken.Promising.X64.isa}
    (ht : (loadProg (kernel n) E Λ prog syms mem).1.threads[tid]? = some t) :
    WordsNone Λ (abi.dmem t.st) :=
  ((privInv_load (n := n) (mem := mem) (wideSt_threadAt hw _ _ _) hE).dmemPriv tid t ht).wordsNone hwf hE

/-- **Along every run from the load, no thread loads a heap or image
word**, for a `wideIn` program and an entry stack clear of the layout. -/
theorem wordsNone_run_of_wide {prog : List (Directive × Nat)} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hw : wideIn (prog.map (·.1)) = true) (hwf : Λ.WF) (hE : E.clear Λ = true) {tr : List Ev} {c : (machine (kernel n)).Cfg}
    (h : (machine (kernel n)).Run μ (loadProg (kernel n) E Λ prog syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (ht : c.1.threads[tid]? = some t) :
    WordsNone Λ (abi.dmem t.st) :=
  ((privInv_run (privInv_load (wideSt_threadAt hw _ _ _) hE) h).dmemPriv tid t ht).wordsNone hwf hE

/-- **The entry state's memory loads no heap or image word**: its keys are
the entry stack's, clear of the layout. -/
theorem wordsNone_stackMem (hwf : Λ.WF) (hE : E.clear Λ = true) : WordsNone Λ E.stackMem :=
  wordsNone_of_keys (fun a ha => .inl ((mem_stackMem (Entry.clear_disjoint hE).1 a).mp ha)) hwf hE

section Place

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}

/-- **`PrivInv` at the load of a placed output**, at any layout the entry
stack is clear of. -/
theorem privInv_load_ofPlaceOKAt (h : Scc.Cert.PlaceOK.X64.placeOKAt cfg Λ0 o = true) {syms : List (String × Nat)}
    {mem : List (Loc × Val)} (hE : E.clear Λ = true) :
    PrivInv abi WideSt Λ E (loadProg (kernel n) E Λ o.prog syms mem) :=
  privInv_load (Scc.Cert.PlaceOK.X64.wideSt_of_placeOKAt h E _ _) hE

/-- **At the load of a placed output no thread loads a heap or image
word**, at the link with the immediates `i` and an admissible entry. -/
theorem wordsNone_load_ofPlaceOKAt (h : Scc.Cert.PlaceOK.X64.placeOKAt cfg Λ0 o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hE : E.Ok { Λ0 with imms := i }) {tid : Nat} {t : Thread Kraken.Promising.X64.isa}
    (ht : (loadProg (kernel n) E { Λ0 with imms := i } o.prog syms mem).1.threads[tid]? = some t) :
    WordsNone { Λ0 with imms := i } (abi.dmem t.st) :=
  wordsNone_load_of_wide (Scc.Cert.PlaceOK.X64.wideIn_of_placeOKAt h)
    (Scc.Cert.PlaceOK.X64.wf_link_of_placeOKAt i h) hE.1 ht

/-- **Along every run from the load of a placed output no thread loads a
heap or image word**, at the link with the immediates `i` and an admissible
entry: the frames' `WordsNone` (`hwn`) at every reachable thread. -/
theorem wordsNone_run_ofPlaceOKAt (h : Scc.Cert.PlaceOK.X64.placeOKAt cfg Λ0 o = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {syms : List (String × Nat)} {mem : List (Loc × Val)}
    (hE : E.Ok { Λ0 with imms := i }) {tr : List Ev} {c : (machine (kernel n)).Cfg}
    (hr : (machine (kernel n)).Run μ (loadProg (kernel n) E { Λ0 with imms := i } o.prog syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (ht : c.1.threads[tid]? = some t) :
    WordsNone { Λ0 with imms := i } (abi.dmem t.st) :=
  wordsNone_run_of_wide (Scc.Cert.PlaceOK.X64.wideIn_of_placeOKAt h)
    (Scc.Cert.PlaceOK.X64.wf_link_of_placeOKAt i h) hE.1 hr ht

end Place

end Spike.Lib.X64DmemPriv
