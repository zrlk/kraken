/-
**hello.w's child stub and thread worker placed** (AArch64; the twin of
`Wake.PlacedZ`'s `cZA_placed`, `proW_x01`, `head_placed`, `tail_placed`): `PlacedSE` at every node's states of the
spawned child's stub and of `scc_rt_thr_worker` (`SegRP.ZObl`'s `hZc`, `hzT`, `hZEt`, `hZT` at
`X := PlacedSE Λ lbl`), over `Spike/Lib/A64HelloPlacedZEnv.lean`'s packet place map. Packet word `i` is the machine
word `wv w i` (`w.w0`, then `w.w2 .. w.w5`; `w.w1`, the buffer's offset `0`, is no packet word); the code keeps
it

    the stub (`childJ`)                    x9, x11 .. x14
    the thread worker's entry, prologue    x0, x2 .. x5         (`thrJE`; the prologue writes x9, x10, sp, x29)
    the thread worker's head (`thrJ`)      −80, −64 .. −40

and the tail's control `cS2` reads nothing.

Differences from wake's: six machine words (`Child.Words`) carry the five packet words where wake's two carry two,
so the place maps are `Nat`-indexed (`stR`, `thR`, `slK`) into `placedSE_kidH_at` (the env file's `placed_kidH`
at `pkRep_of`); the prologue keeps `x0`, `x2 .. x5` (`proW_x15`, wake's `proW_x01` at five registers); the obligations
are `PlacedSE` at no frame (`placedSE_nil`).

- `stR`, `thR`, `slK`: the places' registers and cells; `placedSE_kidH_at`: `kidH` placed at no frame from the
  places' values.
- `keep_chkHead15`, `keep_chkBr15`, `keep_frameSet15`, `proW_x15`: a prologue keeps `x0`, `x2 .. x5` (one-line
  restatements of `A64HelloProArgs`' `keepA_*`, `proW_args`).
- `zc_placed`, `zT_placed`, `zEt_placed`, `zTT_placed`: `ZObl`'s `hZc`, `hzT`, `hZEt`, `hZT`.
-/
import Spike.Lib.A64HelloPlacedZEnv
import Spike.Lib.A64HelloWorkerSegRP
import Spike.Lib.A64HelloProArgs

namespace Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Place WordPlace placeVal ValRep)
open Spike.Lib.A64WakeMainW (M1 placeVal_x placeVal_cell)
open Spike.Lib.A64Consumer (Placed Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (kidH cS2)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words thrJE thrJ cN childN childJ cBlk cb chB pfxM)
open Spike.Lib.A64.Flow (ND At BlkW NodeW arun dstep AM SO arun_take_reg arun_take_slot chkHead chkBr
  frameSet frSetup chkRegs ldStep ProW dstep_spStr)
open Spike.Lib.A64.Flow.Worker (NodeZA)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {w : Words} {w0 w1 w2 w3 w4 : TermRun.Word}

/-! ## The places -/

/-- The stub's registers: packet word `0` in `x9`, word `i ≥ 1` in `x(10+i)`. -/
def stR : Nat → XReg
  | 0 => .X9 | 1 => .X11 | 2 => .X12 | 3 => .X13 | _ => .X14

/-- The thread worker's entry registers: packet word `0` in `x0`, word `i ≥ 1` in `x(i+1)`. -/
def thR : Nat → XReg
  | 0 => .X0 | 1 => .X2 | 2 => .X3 | 3 => .X4 | _ => .X5

/-- The thread worker's frame cells: packet word `0` at `−80`, word `i ≥ 1` at `−72 + 8i`. -/
def slK : Nat → Int
  | 0 => -80 | 1 => -64 | 2 => -56 | 3 => -48 | _ => -40

/-- **`kidH` placed at no frame** from each packet word's place holding its machine word. -/
theorem placedSE_kidH_at {s : State} (T : Ty) (hv0 : ValRep lbl w0.val w.w0.toNat)
    (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat)
    (hvu : ValRep lbl w4.val w.w5.toNat) (P : Nat → Place M1.I.RegId)
    (hP : ∀ i, placeVal M1 s (P i) = some (wv w i).toNat) :
    PlacedSE Λ lbl s (kidH T w0 w1 w2 w3 w4) [] :=
  placedSE_nil (placed_kidH T (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_of (P := P) hv0 hv1 hv2 hv hvu fun i _ => hP i))

/-! ## A prologue keeps `x0`, `x2 .. x5` -/

section Pro

set_option linter.unusedSimpArgs false

variable {lab : Label → Int64}

/-- One of `x0`, `x2 .. x5`: `ProArgs.ArgR` (kept as a name for this file's prologue lemmas). -/
abbrev R15 (r : XReg) : Prop := ArgR r

theorem keep_chkHead15 (Z : Int64) (r : XReg) (hr : R15 r) :
    ∀ d ∈ chkHead Z, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r :=
  keepA_chkHead Z r hr

theorem keep_chkBr15 (L : Label) (r : XReg) (hr : R15 r) :
    ∀ d ∈ chkBr L, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r :=
  keepA_chkBr L r hr

theorem keep_frameSet15 (Z : Int64) (ps : List (XReg × Int64)) (r : XReg) (hr : R15 r) :
    ∀ d ∈ frameSet Z ps, ∀ am : AM, (dstep lab am d).σ.regs.getXReg r = am.σ.regs.getXReg r :=
  keepA_frameSet Z ps r hr

theorem keep_chkRegs15 (Z : Int64) (rr : Reg64s) (r : XReg) (hr : R15 r) :
    (chkRegs Z rr).getXReg r = rr.getXReg r :=
  keepA_chkRegs Z rr r hr

theorem keep_ldStep15 (v : BitVec 64) (σ : Spike.Lib.A64.Flow.AS) (r : XReg) (hr : R15 r) :
    (ldStep .X10 v σ).regs.getXReg r = σ.regs.getXReg r :=
  keepA_ldStep v σ r hr

/-- **A prologue's states inside `W`** from its entry's, agreeing on `x0`, `x2 .. x5` (wake's `proW_x01` at five
registers; the prologue writes none of them): `ProArgs`' `proW_args`. -/
theorem proW_x15 {W : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, (∀ r : XReg, R15 r → s.st.1.regs.getXReg r = σ.regs.getXReg r) →
      W s c) :
    ProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  proW_args hW

end Pro

/-! ## `ZObl`'s fields -/

section Nodes

set_option hygiene false in
/-- The per-directive goals of `arun_take_reg`/`arun_take_slot` on an eight-directive block. -/
local macro "keep_blk8 " "[" bs:ident,* "]" : tactic =>
  `(tactic| (rintro d hd ⟨pc, o, σ⟩
             simp only [$[$bs:ident],*, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc,
               Spike.Lib.A64.Flow.bcD, Spike.Lib.A64.Flow.bD] at hd
             rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dstep_keep))

variable {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isaLSE2} {R : Region}
  {F : MachineData → Prop} {tp sp0 : BitVec 64} {T : Ty}
  (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat)
  (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hZc`: the stub placed** (the source at `kidH`): packet words in `x9`, `x11 .. x14` (`childJ`), which the
`cbz` and the call block's moves into `x0 .. x5` keep. -/
theorem zc_placed : ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (cN pfxM (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0 i) (cBlk i) := by
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨rfl, -, h9, -, h11, h12, h13, h14, -⟩ := hJ
    obtain rfl : k = 0 := by simpa [cBlk, cb] using hk
    refine ⟨placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.x (stR i).idx)) fun i => ?_, fun _ h => h⟩
    rw [placeVal_x]
    show some (m.regs.getXReg (stR i)).toBitVec.toNat = _
    rw [hA'.regs]
    rcases i with _ | _ | _ | _ | i
    · exact congrArg _ (congrArg _ h9)
    · exact congrArg _ (congrArg _ h11)
    · exact congrArg _ (congrArg _ h12)
    · exact congrArg _ (congrArg _ h13)
    · exact congrArg _ (congrArg _ h14)
  · intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
    obtain ⟨_, rfl, -, h9, -, h11, h12, h13, h14, -⟩ := hJ
    refine ⟨placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.x (stR i).idx)) fun i => ?_, fun _ h => h⟩
    rw [placeVal_x]
    show some (m.regs.getXReg (stR i)).toBitVec.toNat = _
    rcases i with _ | _ | _ | _ | i
    · show some (m.regs.getXReg .X9).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X9 (by keep_blk8 [cBlk, chB]) k]; exact congrArg _ (congrArg _ h9)
    · show some (m.regs.getXReg .X11).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X11 (by keep_blk8 [cBlk, chB]) k]; exact congrArg _ (congrArg _ h11)
    · show some (m.regs.getXReg .X12).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X12 (by keep_blk8 [cBlk, chB]) k]; exact congrArg _ (congrArg _ h12)
    · show some (m.regs.getXReg .X13).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X13 (by keep_blk8 [cBlk, chB]) k]; exact congrArg _ (congrArg _ h13)
    · show some (m.regs.getXReg .X14).toBitVec.toNat = _
      rw [hA'.regs, arun_take_reg .X14 (by keep_blk8 [cBlk, chB]) k]; exact congrArg _ (congrArg _ h14)

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hzT`: the thread worker's prologue placed** (the source at `kidH`): packet words in `x0`, `x2 .. x5`
(`thrJE`), which the prologue keeps (`proW_x15`). -/
theorem zT_placed : ProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F (ms [])
    ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs
    (thrJE (kidH T w0 w1 w2 w3 w4) w tp sp0) :=
  proW_x15 fun σ c hJ s hx => by
    obtain ⟨rfl, h0, -, h2, h3, h4, h5, -⟩ := hJ
    refine placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.x (thR i).idx)) fun i => ?_
    rw [placeVal_x]
    rcases i with _ | _ | _ | _ | i
    · show some (s.st.1.regs.getXReg .X0).toBitVec.toNat = _
      rw [hx .X0 (.inl rfl)]; exact congrArg _ (congrArg _ h0)
    · show some (s.st.1.regs.getXReg .X2).toBitVec.toNat = _
      rw [hx .X2 (.inr (.inl rfl))]; exact congrArg _ (congrArg _ h2)
    · show some (s.st.1.regs.getXReg .X3).toBitVec.toNat = _
      rw [hx .X3 (.inr (.inr (.inl rfl)))]; exact congrArg _ (congrArg _ h3)
    · show some (s.st.1.regs.getXReg .X4).toBitVec.toNat = _
      rw [hx .X4 (.inr (.inr (.inr (.inl rfl))))]; exact congrArg _ (congrArg _ h4)
    · show some (s.st.1.regs.getXReg .X5).toBitVec.toNat = _
      rw [hx .X5 (.inr (.inr (.inr (.inr rfl))))]; exact congrArg _ (congrArg _ h5)

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hZEt`: the thread worker's head placed** (the source at `kidH`): packet words in the frame's cells
`−80`, `−64 .. −40` (`thrJ`), which the head's loads into `x0 .. x5` keep; the cells in the region (`hlo`, `hhi`). -/
theorem zEt_placed (hlo : R.lo ≤ -80) (hhi : -32 ≤ R.hi) : NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ (kidH T w0 w1 w2 w3 w4) w tp sp0)
      (fun _ c => c = wcP w0 w1 w2 w3 w4) .e) HThrHead.thE := by
  intro s σ c _ _ _ _ _ _ hJ k _ m hA' _
  obtain ⟨rfl, h80, -, h64, h56, h48, h40, -⟩ := hJ
  refine ⟨placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .slot (R.addr (slK i)).toNat) fun i => ?_, fun _ h => h⟩
  rcases i with _ | _ | _ | _ | i
  · show placeVal M1 _ (.slot (R.addr (-80)).toNat) = _
    rw [placeVal_cell hA' (show R.Off (-80) from ⟨by decide, hlo, by omega⟩) _ rfl,
      arun_take_slot (-80) (by keep_blk [HThrHead.thE]) k, h80]; rfl
  · show placeVal M1 _ (.slot (R.addr (-64)).toNat) = _
    rw [placeVal_cell hA' (show R.Off (-64) from ⟨by decide, by omega, by omega⟩) _ rfl,
      arun_take_slot (-64) (by keep_blk [HThrHead.thE]) k, h64]; rfl
  · show placeVal M1 _ (.slot (R.addr (-56)).toNat) = _
    rw [placeVal_cell hA' (show R.Off (-56) from ⟨by decide, by omega, by omega⟩) _ rfl,
      arun_take_slot (-56) (by keep_blk [HThrHead.thE]) k, h56]; rfl
  · show placeVal M1 _ (.slot (R.addr (-48)).toNat) = _
    rw [placeVal_cell hA' (show R.Off (-48) from ⟨by decide, by omega, by omega⟩) _ rfl,
      arun_take_slot (-48) (by keep_blk [HThrHead.thE]) k, h48]; rfl
  · show placeVal M1 _ (.slot (R.addr (-40)).toNat) = _
    rw [placeVal_cell hA' (show R.Off (-40) from ⟨by decide, by omega, by omega⟩) _ rfl,
      arun_take_slot (-40) (by keep_blk [HThrHead.thE]) k, h40]; rfl

/-- **`ZObl.hZT`: the thread worker's tail placed** (the source at `cS2`, reading nothing). -/
theorem zTT_placed : ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label (cS2 w0 w1 w2 w3 w4) tp i) (HThrTail.blkN i) := by
  intro i
  cases i <;> intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _ <;>
    first | obtain ⟨rfl, -⟩ := hJ | obtain rfl := hJ
  all_goals exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

end Nodes

end Spike.Lib.A64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zc_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zc_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zT_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zT_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zEt_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zEt_placed

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zTT_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zTT_placed
