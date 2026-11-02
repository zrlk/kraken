/-
**hello.w's spawned child, at the source** (x86-64; the twin of `Spike/Lib/HelloSplit.lean`): the spawn leaves the
child at `tail worker [] (var "a") []` on the packet's five words (the slice's three, the flag's, main's
`ThreadId`); its tail call enters `worker`'s body, whose two `split`s and `unpack` bind `j`, `c` and `sl`: the
control `wcP` at the call of `print`. `print` returns into `wcR`, at the `store rel c 1`.

- `slTy`, `pktTy`: the slice's and the spawn packet's types.
- `workerTyH`, `workerRestH`, `workerCallH`, `workerBodyH`, `workerD`: `worker`'s argument type and body;
  `worker_find`: `worker` in `helloSrc`.
- `wcP w0 w1 w2 w3 w4`: the control at `let u = call print [q] sl`; `kid_splitH`: the child's tail call, the
  `split`s and the `unpack`, to `wcP`; `wcP_call`: its term and `sl`'s words.
- `wcR`: the control after `print` returned (`u` bound to `()`), at the `store`; `wcR_pop`: the return's landing
  (`SrcCalls.popTh` of the call's frame) is at `wcR`.

Unlike AArch64, the source is x86-64's reading `X64HelloSrc.helloSrc` and rodata's slice type
`X64HelloRodataSrc.sliceTyP` (`HelloSplit` reaches `HelloSrc`, which imports AArch64's syntax). `slTy` and
`pktTy` (AArch64: `HelloMainPreSrc`'s) are defined here, so that the child's terms do not wait on main's source
module; the definitions are otherwise `HelloSplit`'s, token for token.
-/
import Spike.Lib.X64HelloRodataSrc
import Spike.Lib.SrcCalls
import Spike.Lib.SrcFrames

namespace Spike.Lib.X64HelloSplit

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStepS LocalRunS)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloRodataSrc (sliceTyP)

/-- The slice's type, `∃ m. (([u8; m] pub, m), Int)`. -/
abbrev slTy : Ty := .iex sliceTyP

/-- The spawn packet's type, `((slice, flag), ThreadId)`. -/
abbrev pktTy : Ty := .prod (.prod slTy (.ptr .pub .int)) .tid

/-- `worker`'s argument type: the packet `((slice, flag), ThreadId)`. -/
abbrev workerTyH : Ty := pktTy

/-- `worker`'s body after `print`: `store rel c 1`, `unpark j`, `ret ()`. -/
def workerRestH : Expr :=
  .let_ "d" (.store true (.var "c") (.lit 1) none) (.let_ "w" (.ext .unpark (.var "j")) (.ret .unit))

/-- `worker`'s body at the call of `print`. -/
def workerCallH : Expr := .let_ "u" (.call "print" ["q"] (.var "sl") []) workerRestH

/-- `worker`'s body. -/
def workerBodyH : Expr :=
  .split (.var "a") "slc" "j" <| .split (.var "slc") "sl0" "c" <| .unpack (.var "sl0") "q" "sl" workerCallH

/-- `worker` in `helloSrc`. -/
def workerD : Decl :=
  { name := "worker", tparams := [], idx := [], arg := "a", argTy := workerTyH, retTy := .unit, body := workerBodyH }

theorem worker_find : helloSrc.find? (·.name == "worker") = some workerD := rfl

/-- The environment at the call of `print`: `sl`, `c`, `j` bound to the packet's words. -/
def envP (w0 w1 w2 w3 w4 : Word) : Env :=
  [("sl", sliceTyP, [w0, w1, w2]), ("c", .ptr .pub .int, [w3]), ("sl0", slTy, [w0, w1, w2]),
   ("j", .tid, [w4]), ("slc", .prod slTy (.ptr .pub .int), [w0, w1, w2, w3]), ("a", workerTyH, [w0, w1, w2, w3, w4])]

/-- **The child's control at the call of `print`.** -/
def wcP (w0 w1 w2 w3 w4 : Word) : Ctl := ⟨workerCallH, envP w0 w1 w2 w3 w4, none⟩

theorem wcP_call (w0 w1 w2 w3 w4 : Word) :
    (wcP w0 w1 w2 w3 w4).term = .let_ "u" (.call "print" ["q"] (.var "sl") []) workerRestH ∧
      evalAt (wcP w0 w1 w2 w3 w4).env (.var "sl") = some (sliceTyP, [w0, w1, w2]) ∧
      (wcP w0 w1 w2 w3 w4).hold = none :=
  ⟨rfl, rfl, rfl⟩

/-- **The child's tail call, `split`s and `unpack`**: from the spawn's `tail worker [] (var "a") []` on the
packet's five words, to `wcP`. -/
theorem kid_splitH {p : Prog} (hd : p.find? (·.name == "worker") = some workerD) {T : Ty}
    (w0 w1 w2 w3 w4 : Word) :
    LocalRunS p ⟨.tail "worker" [] (.var "a") [], [("a", T, [w0, w1, w2, w3, w4])], none⟩ (wcP w0 w1 w2 w3 w4) := by
  refine .step (localStepS_tail rfl hd rfl) ?_
  refine .step (localStepS_split (us := [.one, .one, .one, .one]) rfl rfl rfl) ?_
  refine .step (localStepS_split (us := [.one, .one, .one]) rfl rfl rfl) ?_
  exact .single (localStepS_unpack rfl rfl)

/-- **The child's control after `print` returned**: `u` bound to `()`, at the `store rel c 1`. -/
def wcR (w0 w1 w2 w3 w4 : Word) : Ctl := ⟨workerRestH, ("u", .unit, []) :: envP w0 w1 w2 w3 w4, none⟩

/-- **The return out of `print` lands at `wcR`**: popping the call's frame with no result words. -/
theorem wcR_pop (th : TTh) (w0 w1 w2 w3 w4 : Word) (rest : List Frame) :
    (SrcCalls.popTh th ⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩ rest []).term = (wcR w0 w1 w2 w3 w4).term ∧
      (SrcCalls.popTh th ⟨"u", workerRestH, envP w0 w1 w2 w3 w4, [], .unit⟩ rest []).env =
        (wcR w0 w1 w2 w3 w4).env :=
  ⟨rfl, rfl⟩

/-- The child reaches `wcP` in hello's own source. -/
example (w0 w1 w2 w3 w4 : Word) :
    LocalRunS helloSrc ⟨.tail "worker" [] (.var "a") [], [("a", pktTy, [w0, w1, w2, w3, w4])], none⟩
      (wcP w0 w1 w2 w3 w4) :=
  kid_splitH worker_find w0 w1 w2 w3 w4

end Spike.Lib.X64HelloSplit

/-- info: 'Spike.Lib.X64HelloSplit.kid_splitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSplit.kid_splitH
