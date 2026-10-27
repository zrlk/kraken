/-
**`hello1`'s `main` under the source, from the setup block's return**: a
corollary of the per-construct lemmas of `Spike/Lib/SrcCalls.lean` on
`hello1o`, `hello1.w`'s program with `print` linked (`printLD`, `printD`).
From thread 0 at the setup block's `ret` of a slice `(b, 2, 13)` on the
wrapper's frame, with `b` the start of a location whose two words hold the
latest messages `rdK1`, `rdK2`, the source emits `Hello, world\n` and then
`exit 0` (`hello1_main_src`).

- `hello1o`, `mainD`: the linked program and `main` (checked against
  `hello1Src` by `#guard`).
- `helloBytes`, `printBytes_hello`: the 13 bytes, read lane by lane from the
  two words.
- `hello1_main_src`: `setup_ret_src`, `split` and `unpack`
  (`LocalRunS.run_source_top_nil`), then `call_print_src` into `ret 0`.
-/
import Spike.Lib.SrcCalls

namespace Spike.Test.Hello1MainSrc

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.PrintSrc Spike.Lib.SrcCalls Spike.Lib.Hello1Src
open Scc.Sem.MemRel (SLatest)

/-- `hello1.w`'s `main`. -/
def mainD : Decl :=
  { name := "main", tparams := [], idx := [], arg := "a",
    argTy := .prod (.iex sliceTy) (.ptr .pub .void), retTy := .int,
    body :=
      .split (.var "a") "sl0" "me" <|
      .unpack (.var "sl0") "q" "sl" <|
      .let_ "u" (.call "print" ["q"] (.var "sl") []) <|
      .ret (.lit 0) }

/-- `hello1.w`'s program with `print` linked: `printL`, `print`, then the
setup block `rodata` and `main`. -/
def hello1o : Prog := printLD :: printD :: hello1Src.tail

#guard reprStr hello1Src.getLast? == reprStr (some mainD)
#guard reprStr hello1o.tail.tail == reprStr hello1Src.tail

/-- The first word of `hello1.w`'s bytes: `Hello, w`. -/
def rdK1 : Nat := 8583909746840200520

/-- The second word of `hello1.w`'s bytes: `orld\n`. -/
def rdK2 : Nat := 44634501743

/-- The words of the slice: `rdK1`, then `rdK2`. -/
def helloW (i : Nat) : Nat := if i = 0 then rdK1 else rdK2

/-- `main`'s environment at the call of `print`, after `split` and `unpack`. -/
def mainEnv (mws : List Word) (pw wm wn : Word) : Env :=
  [("sl", sliceTy, [pw, wm, wn]), ("me", .ptr .pub .void, mws), ("sl0", .iex sliceTy, [pw, wm, wn]),
   (mainD.arg, mainD.argTy, [pw, wm, wn] ++ mws)]

/-- `Hello, world\n`. -/
def helloBytes : List Nat := [72, 101, 108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 10]

/-- Thread `th` in `main` at the call of `print`, after `split` and `unpack`. -/
def mainTh (th : TTh) (mws : List Word) (pw wm wn : Word) : TTh :=
  { th with term := .let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0)),
            env := mainEnv mws pw wm wn, σs := [], stack := [] }

theorem printBytes_hello : printBytes helloW 0 (printN 13 2) = helloBytes := by decide

/-- **`hello1`'s `main` from the setup block's return**: thread 0 at `ret a`
on the wrapper's frame alone (`me` bound in its environment), `a` the slice
`(b, 2, 13)` with `b` the start of location `l`, whose words `0` and `1` have
latest messages `rdK1` and `rdK2`, no promises and an exit-free trace: the
source emits `Hello, world\n`, then `exit 0`. -/
theorem hello1_main_src {P : SrcParams} (hP : UsesWc P hello1o) {s : Cfg} {th : TTh} {a : At} {fe : Env}
    {rty t tm : Ty} {pw wm wn : Word} {mws : List Word} {l j0 j1 : Nat} {m0 m1 : WeakMem.Msg}
    (hi : s.ths[0]? = some th) (ht : th.term = .ret a)
    (hst : th.stack = [⟨"r", setupCont, fe, [], rty⟩]) (hp : th.promises = [])
    (ha : evalAt th.env a = some (t, [pw, wm, wn])) (hme : evalAt fe (.var "me") = some (tm, mws))
    (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hwm : wm.val = .num 2) (hwn : wn.val = .num 13)
    (hl0 : SLatest s.mem ⟨l, 0⟩ j0) (hm0 : s.mem[j0]? = some m0) (hv0 : m0.val = .num rdK1)
    (hl1 : SLatest s.mem ⟨l, 1⟩ j1) (hm1 : s.mem[j1]? = some m1) (hv1 : m1.val = .num rdK2)
    (hx : ∀ c, Event.exit c ∉ s.trace) :
    ∃ s', (source P hello1o).Run s (outEvs helloBytes ++ [.exit 0]) s' := by
  have hT := traceThs_wc hP
  -- the setup block returns into `main`
  have R1 := setup_ret_src (p := hello1o) (d := mainD) hT hi ht hst hp ha hme rfl (noExit_hook hP hx)
  have hnr : ∀ a', mainD.body ≠ .ret a' := fun _ h => by cases h
  rw [mainExit_of_not_ret (set0 hi) hnr] at R1
  -- `split` and `unpack`
  have r2 : LocalRunS hello1o ⟨mainD.body, [(mainD.arg, mainD.argTy, [pw, wm, wn] ++ mws)], none⟩
      ⟨.let_ "u" (.call "print" ["q"] (.var "sl") []) (.ret (.lit 0)), mainEnv mws pw wm wn, none⟩ :=
    .step (localStepS_split rfl rfl rfl) (.single (localStepS_unpack rfl rfl))
  have R2 := r2.run_source_top_nil hT (set0 (th' := enterTop th mainD ([pw, wm, wn] ++ mws)) hi) rfl rfl rfl rfl hp
    hnr (fun _ h => by cases h) (noExit_hook hP hx)
  simp only [set!_set!] at R2
  change (source P hello1o).Run _ [] { s with ths := s.ths.set! 0 (mainTh th mws pw wm wn) } at R2
  -- the call of `print`, into `ret 0`
  have hM : PrintMem s.mem l (printN 13 2) helloW := by
    intro k hk
    have hk' : k < 13 := by simpa [printN] using hk
    by_cases h8 : k < 8
    · have : k / 8 = 0 := Nat.div_eq_of_lt h8
      exact ⟨j0, m0, this ▸ hl0, hm0, by rw [this]; exact hv0⟩
    · have : k / 8 = 1 := by omega
      exact ⟨j1, m1, this ▸ hl1, hm1, by rw [this]; exact hv1⟩
  obtain ⟨th', ht', -, -, hst', -, R3⟩ := call_print_src (P := P) (p := hello1o) hP rfl rfl
    (set0 (th' := mainTh th mws pw wm wn) hi) rfl rfl hp rfl hpw hwm hwn hM hx
  have hex : mainExit (outCfg { s with ths := s.ths.set! 0 (mainTh th mws pw wm wn) } th'
      (printBytes helloW 0 (printN 13 2))) = [.exit 0] := by
    unfold mainExit outCfg
    simp only [set!_set!]
    rw [set0 hi]
    simp only [ht', hst', mainTh]
    rfl
  rw [hex, printBytes_hello] at R3
  exact ⟨_, (R1.trans R2).trans R3⟩

end Spike.Test.Hello1MainSrc
