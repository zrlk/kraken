/-
**`scc_rt_thread_init`'s states inside `W` on x86-64, for any program**
(`tiW_gen`): the obligations `TiW` (`Spike/Lib/X64Ret0.lean`) of every node
of `scc_rt_thread_init`, from an instance's facts (`InstOk`), the function's
code (`threadInitIn`, a field of the runtime's code checks), its phase facts
(`TiPh`), the TCB's six words it writes, and at its call
`scc_rt_stack_take`'s premises (`takeW_gen`) in the callee's region. The
twin of `Spike/Lib/Rt/A64RtTi.lean`.

- **The phase facts** (`TiPh`): each block's phase check at its pc
  (`blkPh`, the rows of `RtNodesOk`, A6), no dead target; each store off
  the sites and in its next pc's phase (`stPcs`, with its size); the blocks
  before the call not in the take's phase. `TiPhAt` is the same with the
  return point at any label (`.x8` after a setup block), `TiPh` at `.x7`.
- **The words**: the TCB's six fields `tcb + 8·j` (`tiAddrs`) mapped in the
  loaded kernel state, unmapped in private memory under the frame condition
  and owned at no phase.
- **Oracle**: `ret0.x`'s `tiW` (`Spike/Lib/X64Ret0I.lean`) without its take
  site premise is this at its instance (`Spike/Test/X64RtTi.lean`).
-/
import Spike.Lib.Rt.X64RtTake

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW tiN tiX7 tiTake tiCall tiCall_ok lockA freeNA nextA stacksA StackM
  storeBlks_eq bAddr_rcx)
open Scc.Cert.Rt.X64 (blockAtB)

namespace Ti

open Spike.Lib.X64.Flow.Ret0.ThreadInit

/-- The TCB's six fields' addresses `tcb + 8·j`. -/
def tiAddrs (tcb : BitVec 64) : List (BitVec 64) :=
  [tcb + BitVec.ofNat 64 (8 * 0), tcb + BitVec.ofNat 64 (8 * 1), tcb + BitVec.ofNat 64 (8 * 2),
    tcb + BitVec.ofNat 64 (8 * 3), tcb + BitVec.ofNat 64 (8 * 4), tcb + BitVec.ofNat 64 (8 * 5)]

/-- The stores' pcs and sizes. -/
def stPcs (lab : Label → Int64) : List (Int64 × Nat) :=
  [(lab x7L + Int64.ofNat 48, 3), (lab x7L + Int64.ofNat 59, 4), (lab x7L + Int64.ofNat 74, 4),
    (lab x7L + Int64.ofNat 89, 4), (lab x7L + Int64.ofNat 101, 4), (lab x7L + Int64.ofNat 113, 4)]

/-- The pcs before the call. -/
def preTkPcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat 0, lab entryL + Int64.ofNat 0, lab entryL + Int64.ofNat 7]

/-- **`scc_rt_thread_init`'s phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`, returning to `ra x7L`. -/
structure TiPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (lab ra : Label → Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat 0) (ra fnL) tiPro = true
  entry : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 0) (ra entryL) tiArg = true
  c7 : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 7) (ra entryL) tiCall = true
  x7 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 0) (ra x7L) tiSp = true
  f1 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 51) (ra x7L) tiF1 = true
  f2 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 63) (ra x7L) tiZ = true
  f3 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 78) (ra x7L) tiZ = true
  f4 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 93) (ra x7L) tiF4 = true
  f5 : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 105) (ra x7L) tiF5 = true
  ret : blkPh okPc ph (fun _ => false) lab (lab x7L + Int64.ofNat 117) (ra x7L) tiRet = true
  st : ∀ pz ∈ stPcs lab, okPc pz.1.toBitVec.toNat = true ∧
    ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat
  noTk : ∀ p ∈ preTkPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s

/-- The stores' pcs and sizes with the return point at `x` (`stPcs` at
`.x7`). -/
def stPcsAt (lab : Label → Int64) (x : Label) : List (Int64 × Nat) :=
  [(lab x + Int64.ofNat 48, 3), (lab x + Int64.ofNat 59, 4), (lab x + Int64.ofNat 74, 4),
    (lab x + Int64.ofNat 89, 4), (lab x + Int64.ofNat 101, 4), (lab x + Int64.ofNat 113, 4)]

theorem stPcsAt_x7 (lab : Label → Int64) : stPcsAt lab x7L = stPcs lab := rfl

/-- **`scc_rt_thread_init`'s phase facts with its return point at `x`**:
`TiPh` with `.x7` replaced by `x` (x86-64 numbers the `.x` labels per
program: `.x8` after a setup block, `Ret0.ThreadInit.threadInitInAt`). At
`.x7` it is `TiPh` (`TiPhAt.toTiPh`, `TiPh.toAt`). -/
structure TiPhAt (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (lab ra : Label → Int64) (x : Label) :
    Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat 0) (ra fnL) tiPro = true
  entry : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 0) (ra entryL) tiArg = true
  c7 : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 7) (ra entryL) tiCall = true
  x7 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 0) (ra x) tiSp = true
  f1 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 51) (ra x) tiF1 = true
  f2 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 63) (ra x) tiZ = true
  f3 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 78) (ra x) tiZ = true
  f4 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 93) (ra x) tiF4 = true
  f5 : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 105) (ra x) tiF5 = true
  ret : blkPh okPc ph (fun _ => false) lab (lab x + Int64.ofNat 117) (ra x) tiRet = true
  st : ∀ pz ∈ stPcsAt lab x, okPc pz.1.toBitVec.toNat = true ∧
    ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat
  noTk : ∀ p ∈ preTkPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s

section At

variable {okPc : Nat → Bool} {ph : Nat → Nat} {Tk : State → Prop} {lab ra : Label → Int64}

/-- `TiPhAt` at `.x7` is `TiPh`. -/
theorem TiPhAt.toTiPh (h : TiPhAt okPc ph Tk lab ra x7L) : TiPh okPc ph Tk lab ra :=
  ⟨h.e, h.entry, h.c7, h.x7, h.f1, h.f2, h.f3, h.f4, h.f5, h.ret, h.st, h.noTk⟩

/-- `TiPh` is `TiPhAt` at `.x7`. -/
theorem TiPh.toAt (h : TiPh okPc ph Tk lab ra) : TiPhAt okPc ph Tk lab ra x7L :=
  ⟨h.e, h.entry, h.c7, h.x7, h.f1, h.f2, h.f3, h.f4, h.f5, h.ret, h.st, h.noTk⟩

theorem tiPhAt_x7_iff : TiPhAt okPc ph Tk lab ra x7L ↔ TiPh okPc ph Tk lab ra := ⟨TiPhAt.toTiPh, TiPh.toAt⟩

end At

theorem tiPro_noRet : noRetBlk tiPro = true := by rfl
theorem tiArg_noRet : noRetBlk tiArg = true := by rfl
theorem tiCall_noRet : noRetBlk tiCall = true := by rfl
theorem tiSp_noRet : noRetBlk tiSp = true := by rfl
theorem tiF1_noRet : noRetBlk tiF1 = true := by rfl
theorem tiZ_noRet : noRetBlk tiZ = true := by rfl
theorem tiF4_noRet : noRetBlk tiF4 = true := by rfl
theorem tiF5_noRet : noRetBlk tiF5 = true := by rfl

end Ti

/-! ## The nodes and obligations at any return point

`Ret0.tiN`/`Ret0.TiW` (`Spike/Lib/X64Ret0.lean`) name `scc_rt_thread_init`'s
return point `.x7`; x86-64 numbers the `.x` labels per program (`.x8` after
a setup block), so here they are at any label `x`, each `rfl` at `.x7`
(`tiNAt_x7`, `tiWAt_x7`). -/

section NodesAt

open Spike.Lib.X64.Flow.Ret0 Spike.Lib.X64.Flow.Ret0.ThreadInit

variable (lab : Label → Int64) (q : TiG) (x : Label)

/-- **The nodes with the return point at `x`** (`tiN` at `.x7`). -/
def tiNAt : TI → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Pre q.g q.tcb σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ⟩
  | .c7 => ⟨lab entryL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ ∧
      σ.regs.rdi.toBitVec = StackTake.size0⟩
  | .call => ⟨lab StackTake.fnL, ⟨-48, []⟩, fun σ c => (c = q.c0 ∧ (∀ p ∈ s0 q.g q.tcb, σ.slot p.1 = p.2) ∧
      σ.regs.rsp.toBitVec = q.g.sp - 48#64 ∧ σ.regs.rbp.toBitVec = q.g.sp - 8#64 ∧
      σ.regs.rdi.toBitVec = StackTake.size0) ∧ σ.slot (-48) = (lab x).toBitVec⟩
  | .x7 => ⟨lab x, ⟨-40, []⟩, fun σ c => c = q.c0 ∧ Fr q.g (s0 q.g q.tcb) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q⟩
  | .st0 => ⟨lab x + Int64.ofNat 48, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = q.tcb ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f1 => ⟨lab x + Int64.ofNat 51, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st1 => ⟨lab x + Int64.ofNat 59, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q + 4096#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f2 => ⟨lab x + Int64.ofNat 63, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st2 => ⟨lab x + Int64.ofNat 74, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f3 => ⟨lab x + Int64.ofNat 78, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st3 => ⟨lab x + Int64.ofNat 89, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = 0#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f4 => ⟨lab x + Int64.ofNat 93, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st4 => ⟨lab x + Int64.ofNat 101, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .f5 => ⟨lab x + Int64.ofNat 105, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩
  | .st5 => ⟨lab x + Int64.ofNat 113, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ ∧
      σ.regs.rax.toBitVec = tiBase lab q + 16384#64 ∧ σ.regs.rcx.toBitVec = q.tcb⟩
  | .ret => ⟨lab x + Int64.ofNat 117, oI, fun σ c => c = q.c0 ∧ Fr q.g (s1 q.g q.tcb (tiBase lab q)) σ⟩

/-- The return point's node with the frame's `%rbp` offset fixed (`tiX7` at
`.x7`). -/
def tiX7At : ND := ⟨lab x, oI, (tiNAt lab q x .x7).J⟩

theorem tiNAt_x7 : tiNAt lab q x7L = tiN lab q := by
  funext i; cases i <;> rfl

theorem tiX7At_x7 : tiX7At lab q x7L = tiX7 lab q := rfl

end NodesAt

open Spike.Lib.X64.Flow.Ret0 (tiX7) in
/-- **`scc_rt_thread_init`'s node obligations with its return point at `x`**
(`Ret0.TiW` at `.x7`, `tiWAt_x7`). -/
def TiWAt (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F M : MachineData → Prop) (q : TiG) (x : Label) : TI → Prop
  | .e => BlkW W K exe endPc R F (tiNAt (_root_.Executable.labels exe).label q x .e) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiPro
  | .entry => BlkW W K exe endPc R F (tiNAt (_root_.Executable.labels exe).label q x .entry) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiArg
  | .c7 => BlkW W K exe endPc R F (tiNAt (_root_.Executable.labels exe).label q x .c7) tiCall
  | .call => ∀ g, g.ra = ((_root_.Executable.labels exe).label x).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TakeW W K exe endPc (R.callee (-48 - 0) (-200) 8) F M (tiTake q g) i
  | .x7 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiX7At (_root_.Executable.labels exe).label q x) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiSp
  | .st0 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st0)
  | .f1 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .f1) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiF1
  | .st1 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st1)
  | .f2 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .f2) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiZ
  | .st2 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st2)
  | .f3 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .f3) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiZ
  | .st3 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st3)
  | .f4 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .f4) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiF4
  | .st4 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st4)
  | .f5 => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .f5) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiF5
  | .st5 => NodeW W K exe endPc R (fun m => F m ∧ M m) (tiNAt (_root_.Executable.labels exe).label q x .st5)
  | .ret => BlkW W K exe endPc R (fun m => F m ∧ M m)
      (tiNAt (_root_.Executable.labels exe).label q x .ret) Spike.Lib.X64.Flow.Ret0.ThreadInit.tiRet

theorem tiWAt_x7 {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F M : MachineData → Prop} {q : TiG} (i : TI) :
    TiWAt W K exe endPc R F M q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L i = TiW W K exe endPc R F M q i := by
  cases i <;> rfl

set_option hygiene false in
/-- A block of `scc_rt_thread_init` before the call, no `ret`, no dead
target. -/
local macro "iblk0 " ok:term:max f:term:max nr:term:max : tactic =>
  `(tactic| (
    dsimp only [TiWAt]
    rw [hI.labOk]
    exact blkW_pre hI (by assumption) (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega)
      (hC _ fun _ _ hJ => hJ.1) $f (hnr $nr) (fun _ _ _ => rfl) (hph.noTk _ (by simp [preTkPcs]))))

set_option hygiene false in
/-- A block of `scc_rt_thread_init` after the take, no `ret`, no dead
target. -/
local macro "iblk " ok:term:max f:term:max nr:term:max : tactic =>
  `(tactic| (
    dsimp only [TiWAt]
    rw [hI.labOk]
    exact blkW_post hI (by assumption) (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega)
      (hC _ fun _ _ hJ => hJ.1) $f (hnr $nr) (fun _ _ _ => rfl) hsub hSM))

set_option hygiene false in
/-- The store of TCB field `j` (`z` bytes at the return point `x` + `off`) of
`scc_rt_thread_init`, after the take. -/
local macro "ist " j:term:max k:term:max off:term:max z:term:max : tactic =>
  `(tactic| (
    dsimp only [TiWAt]
    rw [hI.labOk]
    have hs := hph.st (lab x + Int64.ofNat $off, $z) (by simp [stPcsAt])
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ tiAddrs q.tcb := by simp [tiAddrs]
    exact nodeW_st_post (b := .rcx) (k := $k) (r := .rax) (z := $z) (l := x) (off := $off)
      (a := q.tcb + BitVec.ofNat 64 (8 * $j)) (p := lab x + Int64.ofNat $off) hI hown (by assumption) rfl rfl
      (hC _ fun _ _ hJ => hJ.1) hs.1 hs.2
      (fun σ _ hJ => by rw [bAddr_rcx hJ.2.2.2]; exact congrArg (q.tcb + ·) (by decide))
      (hmF _ ha) (hunF _ ha) (hnoF _ ha) hsub))

set_option maxHeartbeats 800000 in
open Ti Take Spike.Lib.X64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s states are inside `SFacts`, its return point at
any label `x`** (`.x8` after a setup block), for any program with the
function's code there (`hin`, `threadInitInAt`), in any region holding its frame and the
take's below, with the source control `c0` (`hC0`, its facts), returning to
`ra x` (`hra`), its phase facts at `x` (`hph`, `TiPhAt`), the TCB's six words mapped
(`hmF`), unmapped in private memory under the frame condition (`hunF`) and
owned at no phase (`hnoF`), the take's range in the pool (`hsub`) kept by
the writes of both regions (`hSM`, `hSM'`), and at its call
`scc_rt_stack_take`'s premises of `takeW_gen` (`hin'` to `hdisj`), returning
to `x`. `tiW_gen` is it at `.x7`. -/
theorem tiWAt_gen {x : Label} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : threadInitInAt cells x = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra x).toBitVec) (hph : TiPhAt okPc ph Tk lab ra x)
    (hmF : ∀ a ∈ tiAddrs q.tcb, Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ tiAddrs q.tcb, ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hin' : Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn cells = true) (hphT : TakePh okPc ph Tk ownOf μ lab fun _ => lab x)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hrS : rS = ⟨(stacksA lab + q.k0).toNat, 16384⟩) (hdisj : Λ.rodata.Disjoint Λ.stackPool) :
    ∀ i, TiWAt (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (StackM rS) q x i := by
  have h := hin
  simp only [threadInitInAt, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h, hst⟩ := h
  repeat (obtain ⟨h, _⟩ := h)
  repeat (obtain ⟨_, hst⟩ := hst)
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e => iblk0 tiPro_ok hph.e tiPro_noRet
  case entry => iblk0 tiArg_ok hph.entry tiArg_noRet
  case c7 => iblk0 tiCall_ok hph.c7 tiCall_noRet
  case call =>
    intro g hg j
    rw [hI.labOk] at hg
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    exact takeW_gen hI hown hin' hC0 hR' (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega)
      (tiTake q g) hq hg hphT hmL hmN hmX hunL hunN hunX hrS hsub hdisj hSM' j
  case x7 => iblk tiSp_ok hph.x7 tiSp_noRet
  case st0 => ist 0 0 48 3
  case f1 => iblk tiF1_ok hph.f1 tiF1_noRet
  case st1 => ist 1 8 59 4
  case f2 => iblk tiZ_ok hph.f2 tiZ_noRet
  case st2 => ist 2 16 74 4
  case f3 => iblk tiZ_ok hph.f3 tiZ_noRet
  case st3 => ist 3 24 89 4
  case f4 => iblk tiF4_ok hph.f4 tiF4_noRet
  case st4 => ist 4 32 101 4
  case f5 => iblk tiF5_ok hph.f5 tiF5_noRet
  case st5 => ist 5 40 113 4
  case ret =>
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_post hI (by assumption) rfl tiRet_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run tiRet_ok fun _ _ hJ => by
        dsimp only [tiNAt] at hJ ⊢
        rw [(tiRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) hsub hSM

open Ti Take Spike.Lib.X64.Flow.Ret0.ThreadInit in
/-- **`scc_rt_thread_init`'s states are inside `SFacts`**, for any program
with the function's code (`hin`), in any region holding its frame and the
take's below, with the source control `c0` (`hC0`, its facts), returning to
`ra x7L` (`hra`), its phase facts (`hph`), the TCB's six words mapped
(`hmF`), unmapped in private memory under the frame condition (`hunF`) and
owned at no phase (`hnoF`), the take's range in the pool (`hsub`) kept by
the writes of both regions (`hSM`, `hSM'`), and at its call
`scc_rt_stack_take`'s premises of `takeW_gen` (`hin'` to `hdisj`), returning
to `.x7` (`tiWAt_gen` at `.x7`). -/
theorem tiW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : threadInitIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra x7L).toBitVec) (hph : TiPh okPc ph Tk lab ra)
    (hmF : ∀ a ∈ tiAddrs q.tcb, Scc.Sem.Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ a ∈ tiAddrs q.tcb, ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j)
    (hsub : rS.Sub Λ.stackPool) (hSM : FStable R (StackM rS))
    (hSM' : FStable (R.callee (-48 - 0) (-200) 8) (StackM rS))
    (hin' : Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn cells = true) (hphT : TakePh okPc ph Tk ownOf μ lab fun _ => lab x7L)
    (hmL : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨lockA lab, 8⟩ = true)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨freeNA lab, 8⟩ = true)
    (hmX : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨nextA lab, 8⟩ = true)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hrS : rS = ⟨(stacksA lab + q.k0).toNat, 16384⟩) (hdisj : Λ.rodata.Disjoint Λ.stackPool) :
    ∀ i, TiW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (StackM rS) q i := fun i =>
  tiWAt_x7 (W := fun s c => SFacts Λ μ own rS Tk lbl s c) i ▸
    tiWAt_gen hI hown hin hC0 hR hlo hhi q hq hra hph.toAt hmF hunF hnoF hsub hSM hSM' hin' hphT hmL hmN hmX hunL
      hunN hunX hrS hdisj i

end Spike.Lib.X64.Rt
