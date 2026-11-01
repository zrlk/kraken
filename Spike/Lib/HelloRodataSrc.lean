/-
**`hello.w`'s setup block `rodata` as a source run of one frame** (C2,
source half): `Hello1RodataSrc`'s controls, plus the publication `let s =
publish b` after the second exchange. The lowered `wc_rodata` matches it
with one `dmb ishst` after the second exchange's store.

- `rdBody` and its tails `eM` … `eRet`; `rdBody_eq`: it is `rodata`'s body
  in `HelloSrc.helloSrc`; `sliceTyP`: hello's published slice type.
- `rdC0` … `rdC3`, `rdCA_store`, `rdC2_store`, `rdC1_next`, `rdC3_next`:
  as in `Hello1RodataSrc` (entry, allocation, the two lane stores), at
  hello's terms; the environments are hello1's (`Hello1RodataSrc.env0` …
  `env4`, `bBind`).
- `rdC4 l ini wo0 wo1`: after the second exchange, at `let s = publish b`;
  `rdC5`: past it, `s` bound to `b`'s word at the published buffer type.
- `rdCP_pub`: the publication is the source's `PubStep .st` from `rdC4` to
  `rdC5` (the source half of the `dmb ishst` row).
- `rdC5_run`: `let n = 13`, the two pairs and the `pack`, to `rdRet` at
  `ret sl`; `rdC4_fence`: the row's `FenceRun` from `rdC4` to `rdRet`.
- `rdRet_ret`: `sl` is `[b, 2, 13]` at the published slice type.
-/
import Spike.Lib.HelloSrc
import Spike.Lib.Hello1RodataSrc

namespace Spike.Lib.HelloRodataSrc

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalStep LocalRun XchgSite PubStep FenceRun)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2 τ8 env0 envN bBind envA env1 env2 env3 env4 rdK1_lt rdK2_lt bufElem_b
  evalAt_b3)
open Scc.Sem (ValRep)

/-! ## The terms -/

/-- **hello's slice type**: `print`'s published signature, the buffer `pub`. -/
def sliceTyP : Ty :=
  .prod (.prod (.refine (.loc .pub (.array (.var 0) τ8)) (.ini (.var 0))) (.intS (.var 0))) .int

def eRet : Expr := .ret (.var "sl")
def ePack : Expr := .let_ "sl" (.pack (.var "sl0") "m" (.iex sliceTyP)) eRet
def eSl0 : Expr := .let_ "sl0" (.pair (.var "sm") (.var "n")) ePack
def eSm : Expr := .let_ "sm" (.pair (.var "s") (.var "m")) eSl0
def eN : Expr := .let_ "n" (.atom (.lit 13)) eSm
def eS : Expr := .let_ "s" (.publish (.var "b")) eN
def eO1 : Expr := .let_ "o1" (.xchgAt (.var "b") (.lit 1) (.var "w1")) eS
def eW1 : Expr := .let_ "w1" (.asLanes false .w8 (.lit rdK2)) eO1
def eO0 : Expr := .let_ "o0" (.xchgAt (.var "b") (.lit 0) (.var "w0")) eW1
def eW0 : Expr := .let_ "w0" (.asLanes false .w8 (.lit rdK1)) eO0
def eB : Expr := .let_ "b" (.newBuf (.var "m") τ8) eW0
def eM : Expr := .let_ "m" (.nameI (.var "two")) eB

/-- `rodata`'s body in hello.w. -/
def rdBody : Expr := .let_ "two" (.atom (.lit 2)) eM

theorem rdBody_eq : helloSrc[2]?.map (·.body) = some rdBody := rfl

theorem rodata_name : helloSrc[2]?.map (·.name) = some "rodata" := rfl

/-! ## The controls -/

/-- The published buffer's type, `ini` elements initialised. -/
def tS (ini : Nat) : Ty := .refine (.loc .pub (.array (.lit 2) (close [] τ8))) (.ini (.lit ini))

/-- The environment after the publication: `s` bound to `b`'s word. -/
def env5 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Env :=
  ("s", tS ini, [cst (.loc ⟨l, 0⟩ 0)]) :: env4 l ini wo0 wo1

/-- The type of the pair `(s, m)`. -/
def tSm (ini : Nat) : Ty := .prod (tS ini) (.intS (.lit 2))

/-- The environment at `ret sl`. -/
def envR (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Env :=
  ("sl", close [] (.iex sliceTyP), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
  ("sl0", .prod (tSm ini) (.intS (.lit 13)), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
  ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
  ("n", .intS (.lit 13), [cst (.num 13)]) :: env5 l ini wo0 wo1

def rdC0 : Ctl := ⟨rdBody, env0, none⟩
def rdCN : Ctl := ⟨eB, envN, none⟩
def rdCA (l : WeakMem.AllocLabel) (ini : Nat) : Ctl := ⟨eW0, envA l ini, none⟩
def rdC1 (l : WeakMem.AllocLabel) (ini : Nat) : Ctl := ⟨eO0, env1 l ini, none⟩
def rdC2 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Ctl := ⟨eW1, env2 l ini wo0, none⟩
def rdC3 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) : Ctl := ⟨eO1, env3 l ini wo0, none⟩
def rdC4 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Ctl := ⟨eS, env4 l ini wo0 wo1, none⟩
def rdC5 (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) : Ctl := ⟨eN, env5 l ini wo0 wo1, none⟩
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

/-- **The second lane store**, source side, at `rdC2 l ini wo0`: the
`asLanes` step to `rdC3`, an exchange site of element 1 at `A + 8`, the
word `rdK2`. -/
theorem rdC2_store {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {ini A : Nat}
    {wo0 : Word} (hl : lbl l = some A) :
    LocalStep p (rdC2 l ini wo0) (rdC3 l ini wo0) ∧
      XchgSite (rdC3 l ini wo0) "o1" (offs ⟨l, 0⟩ 1) τ8 (.var "w1") eS ∧
      ValRep lbl (.loc (offs ⟨l, 0⟩ 1) 0) (A + 8 * 1) ∧ (rdC3 l ini wo0).hold = none ∧
      evalAt (rdC3 l ini wo0).env (.var "w1") = some (τ8, [cst (.num rdK2)]) ∧
      ValRep lbl (cst (.num rdK2)).val rdK2 :=
  LaneStoreSrc.laneStore (c := rdC2 l ini wo0) rfl (by decide) (evalAt_b3 l ini wo0) rfl (bufElem_b ini) hl
    rdK2_lt

/-- The exchange's continuation from `rdC1` is `rdC2` (binding the old
word). -/
theorem rdC1_next (l : WeakMem.AllocLabel) (ini : Nat) (wo0 : Word) :
    (⟨eW1, ("o0", τ8, [wo0]) :: (rdC1 l ini).env, none⟩ : Ctl) = rdC2 l ini wo0 := rfl

/-- The exchange's continuation from `rdC3` is `rdC4`, at the publication. -/
theorem rdC3_next (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    (⟨eS, ("o1", τ8, [wo1]) :: (rdC3 l ini wo0).env, none⟩ : Ctl) = rdC4 l ini wo0 wo1 := rfl

/-- **The publication**: `let s = publish b` at `rdC4` is the source's
`PubStep` at a store fence, to `rdC5` (`s` bound to `b`'s word, the buffer
published). -/
theorem rdCP_pub (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    PubStep .st (rdC4 l ini wo0 wo1) (rdC5 l ini wo0 wo1) :=
  ⟨.inl rfl, rfl, "s", .var "b", eN, (bBind l ini).2.1, tS ini, [cst (.loc ⟨l, 0⟩ 0)], .inl ⟨rfl, rfl⟩, rfl, rfl⟩

/-- **From the publication to `ret sl`**: `let n = 13`, the two pairs and
the `pack`. -/
theorem rdC5_run (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    LocalRun p (rdC5 l ini wo0 wo1) (rdRet l ini wo0 wo1) := by
  refine .step (Spike.Lib.Form.localStep_atom (c := rdC5 l ini wo0 wo1) rfl rfl) ?_
  refine .step (Spike.Lib.Form.localStep_pair (c := ⟨eSm, ("n", .intS (.lit 13), [cst (.num 13)]) ::
    env5 l ini wo0 wo1, none⟩) rfl rfl rfl) ?_
  refine .step (Spike.Lib.Form.localStep_pair (c := ⟨eSl0, ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
    ("n", .intS (.lit 13), [cst (.num 13)]) :: env5 l ini wo0 wo1, none⟩) rfl rfl rfl) ?_
  exact .single (Spike.Lib.Form.localStep_pack (c := ⟨ePack,
    ("sl0", .prod (tSm ini) (.intS (.lit 13)), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) ::
    ("sm", tSm ini, [cst (.loc ⟨l, 0⟩ 0), cst (.num 2)]) ::
    ("n", .intS (.lit 13), [cst (.num 13)]) :: env5 l ini wo0 wo1, none⟩) rfl rfl)

/-- **The `dmb ishst` row's source run**: where the memory side admits the
publication (`P`), the publication then the local run to `ret sl`. -/
theorem rdC4_fence {P : Prop} (hP : P) (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    FenceRun p P .st (rdC4 l ini wo0 wo1) (rdRet l ini wo0 wo1) :=
  .pub hP (rdCP_pub l ini wo0 wo1) (rdC5_run l ini wo0 wo1)

/-- `rdRet` is at `ret sl`, its slice the words of `b`, `m` and `n` at the
published slice type. -/
theorem rdRet_ret (l : WeakMem.AllocLabel) (ini : Nat) (wo0 wo1 : Word) :
    (rdRet l ini wo0 wo1).term = .ret (.var "sl") ∧ (rdRet l ini wo0 wo1).hold = none ∧
      evalAt (rdRet l ini wo0 wo1).env (.var "sl") =
        some (close [] (.iex sliceTyP), [cst (.loc ⟨l, 0⟩ 0), cst (.num 2), cst (.num 13)]) :=
  ⟨rfl, rfl, rfl⟩

end Spike.Lib.HelloRodataSrc

/-- info: 'Spike.Lib.HelloRodataSrc.rdCP_pub' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.HelloRodataSrc.rdCP_pub

/-- info: 'Spike.Lib.HelloRodataSrc.rdC4_fence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRodataSrc.rdC4_fence

/-- info: 'Spike.Lib.HelloRodataSrc.rdC2_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRodataSrc.rdC2_store
