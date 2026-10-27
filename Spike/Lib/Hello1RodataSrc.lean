/-
**`hello1.w`'s setup block `rodata` as a source run of one frame**: the
controls of `rodata`'s body from its entry to its `ret`, and the source
steps between them that the lowered `wc_rodata` matches.

- `rdBody` and its tails `eM` … `eRet`; `rdBody_eq`: it is `rodata`'s
  body in `Hello1Src.hello1Src`.
- `rdC0`: the entry (`u` bound to the unit); `rdCN`: at the buffer
  allocation, after `let two = 2` and `let m = nameI two`
  (`rdC0_run`, two local steps); `rdCN_newBuf`: its allocation facts
  (`newBuf[LanesU8] m` of `2` one-word elements).
- `rdCA l ini`: after the allocation at label `l` (`ini` elements
  initialised), at `let w0 = asLanes U8 K1`; `rdC1`: past it, at the first
  exchange; `rdCA_store`: `LaneStoreSrc.laneStore` there (element 0, word
  `rdK1`).
- `rdC2 … wo0`: after the first exchange (binding the old word `wo0`), at
  `let w1 = …`; `rdC3`: at the second exchange; `rdC2_store`: element 1,
  word `rdK2`.
- `rdC4 … wo1`: after the second exchange; `rdRet`: at `ret sl`, `sl` the
  packed slice `[b, m, n]` (`rdC4_run`, four local steps).
- `rdK1`, `rdK2`: the two lane words (`"Hello, w"`, `"orld\n"`), below
  `2^64`.
-/
import Spike.Lib.Hello1Src
import Spike.Lib.LaneStoreSrc

namespace Spike.Lib.Hello1RodataSrc

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStep LocalRun XchgSite)
open Spike.Lib.Hello1Src (hello1Src sliceTy)
open Scc.Sem (ValRep)

/-! ## The terms -/

/-- The first lane word, `"Hello, w"`. -/
abbrev rdK1 : Nat := 8583909746840200520
/-- The second lane word, `"orld\n"`. -/
abbrev rdK2 : Nat := 44634501743

/-- The element type, `LanesU8`. -/
abbrev τ8 : Ty := .lanes false .w8

def eRet : Expr := .ret (.var "sl")
def ePack : Expr := .let_ "sl" (.pack (.var "sl0") "m" (.iex sliceTy)) eRet
def eSl0 : Expr := .let_ "sl0" (.pair (.var "sm") (.var "n")) ePack
def eSm : Expr := .let_ "sm" (.pair (.var "b") (.var "m")) eSl0
def eN : Expr := .let_ "n" (.atom (.lit 13)) eSm
def eO1 : Expr := .let_ "o1" (.xchgAt (.var "b") (.lit 1) (.var "w1")) eN
def eW1 : Expr := .let_ "w1" (.asLanes false .w8 (.lit rdK2)) eO1
def eO0 : Expr := .let_ "o0" (.xchgAt (.var "b") (.lit 0) (.var "w0")) eW1
def eW0 : Expr := .let_ "w0" (.asLanes false .w8 (.lit rdK1)) eO0
def eB : Expr := .let_ "b" (.newBuf (.var "m") τ8) eW0
def eM : Expr := .let_ "m" (.nameI (.var "two")) eB

/-- **`rodata`'s body.** -/
def rdBody : Expr := .let_ "two" (.atom (.lit 2)) eM

/-- `rdBody` is `rodata`'s body in `hello1Src`. -/
theorem rdBody_eq : hello1Src[1]?.map (·.body) = some rdBody := rfl

/-- `rodata` is `hello1Src`'s second declaration. -/
theorem rodata_name : hello1Src[1]?.map (·.name) = some "rodata" := rfl

/-! ## The controls -/

/-- The entry's environment: `u` bound to the unit. -/
def env0 : Env := [("u", .unit, [])]

/-- The environment at the allocation. -/
def envN : Env := ("m", .intS (.lit 2), [cst (.num 2)]) :: ("two", .intS (.lit 2), [cst (.num 2)]) :: env0

/-- The buffer's binding at label `l`, `ini` elements initialised. -/
def bBind (l : WeakMem.AllocLabel) (ini : Nat) : String × Ty × List Word :=
  ("b", .refine (.loc .own (.array (.lit 2) (close [] τ8))) (.ini (.lit ini)), [cst (.loc ⟨l, 0⟩ 0)])

/-- The environment after the allocation. -/
def envA (l : WeakMem.AllocLabel) (ini : Nat) : Env := bBind l ini :: envN

/-- The environment at the first exchange. -/
def env1 (l : WeakMem.AllocLabel) (ini : Nat) : Env := ("w0", τ8, [cst (.num rdK1)]) :: envA l ini

/-- The environment after the first exchange (old word `wo0`). -/
def env2 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Env := ("o0", τ8, [wo0]) :: env1 l ini

/-- The environment at the second exchange. -/
def env3 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Env := ("w1", τ8, [cst (.num rdK2)]) :: env2 l ini wo0

/-- The environment after the second exchange (old word `wo1`). -/
def env4 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Env := ("o1", τ8, [wo1]) :: env3 l ini wo0

/-- The type of the pair `(b, m)`. -/
def tSm (ini : Nat) : Ty := .prod (.refine (.loc .own (.array (.lit 2) (close [] τ8))) (.ini (.lit ini))) (.intS (.lit 2))

/-- The environment at `ret sl`. -/
def envR (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Env :=
  ("sl", close [] (.iex sliceTy), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
  ("sl0", .prod (tSm ini) (.intS (.lit 13)), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
  ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
  ("n", .intS (.lit 13), [cst (.num 13)]) :: env4 l ini wo0 wo1

def rdC0 : Ctl := ⟨rdBody, env0, none⟩
def rdCN : Ctl := ⟨eB, envN, none⟩
def rdCA (l : WeakMem.AllocLabel) (ini : Nat) : Ctl := ⟨eW0, envA l ini, none⟩
def rdC1 (l : WeakMem.AllocLabel) (ini : Nat) : Ctl := ⟨eO0, env1 l ini, none⟩
def rdC2 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Ctl := ⟨eW1, env2 l ini wo0, none⟩
def rdC3 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Ctl := ⟨eO1, env3 l ini wo0, none⟩
def rdC4 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Ctl := ⟨eN, env4 l ini wo0 wo1, none⟩
def rdRet (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Ctl := ⟨eRet, envR l ini wo0 wo1, none⟩

/-! ## The steps -/

variable {p : Prog}

/-- **From the entry to the allocation**: `let two = 2`, `let m = nameI
two`. -/
theorem rdC0_run : LocalRun p rdC0 rdCN :=
  .step (Spike.Lib.Form.localStep_atom (c := rdC0) rfl rfl)
    (.single (Spike.Lib.Form.localStep_nameI (c := ⟨eM, ("two", .intS (.lit 2), [cst (.num 2)]) :: env0, none⟩)
      rfl rfl))

/-- **The allocation's facts at `rdCN`**: `let b = newBuf[LanesU8] m` with
`m` the number `2`, the closed element type one word. -/
theorem rdCN_newBuf :
    rdCN.term = .let_ "b" (.newBuf (.var "m") τ8) eW0 ∧
      evalAt rdCN.env (.var "m") = some (.intS (.lit 2), [cst (.num 2)]) ∧
      numOf [cst (.num 2)] = some 2 ∧ accs (close [] τ8) = some [.one] ∧ rdCN.hold = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The two lane words are below `2^64`. -/
theorem rdK1_lt : rdK1 < 2 ^ 64 := by decide
theorem rdK2_lt : rdK2 < 2 ^ 64 := by decide

/-- `close []` leaves `LanesU8` as it is. -/
theorem close_τ8 : close [] τ8 = τ8 := rfl

/-- The buffer's element type is `LanesU8`. -/
theorem bufElem_b (ini : Nat) :
    bufElem (.refine (.loc .own (.array (.lit 2) (close [] τ8))) (.ini (.lit ini))) = some (.own, τ8) := rfl

/-- **The first lane store**, source side, at `rdCA l ini` with `l` placed
at `A`: the `asLanes` step to `rdC1`, an exchange site of element 0 at
`A`, the word `rdK1`. -/
theorem rdCA_store {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {ini A : Nat}
    (hl : lbl l = some A) :
    LocalStep p (rdCA l ini) (rdC1 l ini) ∧
      XchgSite (rdC1 l ini) "o0" (offs ⟨l, 0⟩ 0) τ8 (.var "w0") eW1 ∧
      ValRep lbl (.loc (offs ⟨l, 0⟩ 0) 0) (A + 8 * 0) ∧ (rdC1 l ini).hold = none ∧
      evalAt (rdC1 l ini).env (.var "w0") = some (τ8, [cst (.num rdK1)]) ∧
      ValRep lbl (cst (.num rdK1)).val rdK1 :=
  LaneStoreSrc.laneStore (c := rdCA l ini) rfl (by decide) rfl rfl (bufElem_b ini) hl rdK1_lt

/-- `b` is not shadowed at the second exchange. -/
theorem evalAt_b3 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) :
    evalAt (env2 l ini wo0) (.var "b") = some ((bBind l ini).2.1, (bBind l ini).2.2) := rfl

/-- **The second lane store**, source side, at `rdC2 l ini wo0`: the
`asLanes` step to `rdC3`, an exchange site of element 1 at `A + 8`, the
word `rdK2`. -/
theorem rdC2_store {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {ini A : Nat}
    {wo0 : Word} (hl : lbl l = some A) :
    LocalStep p (rdC2 l ini wo0) (rdC3 l ini wo0) ∧
      XchgSite (rdC3 l ini wo0) "o1" (offs ⟨l, 0⟩ 1) τ8 (.var "w1") eN ∧
      ValRep lbl (.loc (offs ⟨l, 0⟩ 1) 0) (A + 8 * 1) ∧ (rdC3 l ini wo0).hold = none ∧
      evalAt (rdC3 l ini wo0).env (.var "w1") = some (τ8, [cst (.num rdK2)]) ∧
      ValRep lbl (cst (.num rdK2)).val rdK2 :=
  LaneStoreSrc.laneStore (c := rdC2 l ini wo0) rfl (by decide) (evalAt_b3 l ini wo0) rfl (bufElem_b ini) hl
    rdK2_lt

/-- The exchange's continuation from `rdC1` is `rdC2` (binding the old
word). -/
theorem rdC1_next (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) :
    (⟨eW1, ("o0", τ8, [wo0]) :: (rdC1 l ini).env, none⟩ : Ctl) = rdC2 l ini wo0 := rfl

/-- The exchange's continuation from `rdC3` is `rdC4`. -/
theorem rdC3_next (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    (⟨eN, ("o1", τ8, [wo1]) :: (rdC3 l ini wo0).env, none⟩ : Ctl) = rdC4 l ini wo0 wo1 := rfl

/-- **From the second exchange to `ret sl`**: `let n = 13`, the two pairs
and the `pack`. -/
theorem rdC4_run (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    LocalRun p (rdC4 l ini wo0 wo1) (rdRet l ini wo0 wo1) := by
  refine .step (Spike.Lib.Form.localStep_atom (c := rdC4 l ini wo0 wo1) rfl rfl) ?_
  refine .step (Spike.Lib.Form.localStep_pair (c := ⟨eSm, ("n", .intS (.lit 13), [cst (.num 13)]) ::
    env4 l ini wo0 wo1, none⟩) rfl rfl rfl) ?_
  refine .step (Spike.Lib.Form.localStep_pair (c := ⟨eSl0, ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
    ("n", .intS (.lit 13), [cst (.num 13)]) :: env4 l ini wo0 wo1, none⟩) rfl rfl rfl) ?_
  exact .single (Spike.Lib.Form.localStep_pack (c := ⟨ePack,
    ("sl0", .prod (tSm ini) (.intS (.lit 13)), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
    ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
    ("n", .intS (.lit 13), [cst (.num 13)]) :: env4 l ini wo0 wo1, none⟩) rfl rfl)

/-- `rdRet` is at `ret sl`, its slice the words of `b`, `m` and `n`. -/
theorem rdRet_ret (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    (rdRet l ini wo0 wo1).term = .ret (.var "sl") ∧ (rdRet l ini wo0 wo1).hold = none ∧
      evalAt (rdRet l ini wo0 wo1).env (.var "sl") =
        some (close [] (.iex sliceTy), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) :=
  ⟨rfl, rfl, rfl⟩

end Spike.Lib.Hello1RodataSrc
