/-
**hello.w's child stub and thread worker placed** (x86-64; the twin of `Spike/Lib/A64HelloPlacedZKid.lean`, itself
the twin of `Wake.PlacedZ`'s `cZA_placed`, `xProW_rr`, `head_placed`, `tail_placed`): `PlacedSE` at every node's
states of the spawned child's stub and of `scc_rt_thr_worker` (`SegRP.ZObl`'s `hZc`, `hzT`, `hZEt`, `hZT` at
`X := PlacedSE Λ lbl`), over `Spike/Lib/X64HelloPlacedZEnv.lean`'s packet place map. Packet word `i` is the machine
word `wv w i` (`w.w0`, then `w.w2 .. w.w5`; `w.w1`, the buffer's offset `0`, is no packet word); the code keeps
it

    the stub (`childJ`)                    %r12, %r13, %r14, %r15, %r9
    the thread worker's entry, prologue    %rdi, %rdx, %rcx, %r8, %r9   (`thrJE`; `xProW_args`)
    the thread worker's head (`thrJ`)      −16, −32 .. −56

and the tail's control `cS2` reads nothing.

- `stR`, `thR`, `slK`: the places' registers and cells; `placedSE_kidH_at`: `kidH` placed at no frame from the
  places' values.
- `R15`, `proW_x15`: a prologue keeps `ArgR`'s registers (`X64HelloProArgs`' `xProW_args`).
- `chB_keep5`, `thE_slot`: the stub's call block keeps the stub's registers, the thread worker's `.entry` block
  the frame's cells.
- `zc_placed`, `zT_placed`, `zEt_placed`, `zTT_placed`: `ZObl`'s `hZc`, `hzT`, `hZEt`, `hZT`.

## Differences from the AArch64 version

- The stub holds the packet in `%r12`, `%r13 .. %r15`, `%r9` (`%rbx` the offset word), the thread worker's entry
  in `%rdi`, `%rdx .. %r9`, its head in the cells `−16`, `−32 .. −56` (`-8 .. -48(%rbp)`).
- The thread worker runs in `ZObl`'s re-based region `thrR R` from `sp0 - 8`: `zT_placed`, `zEt_placed` and
  `zTT_placed` are stated at any region, stack top and thread pointer.
- The prologue's lemma is `XProW`'s (`proW_x15` restates `xProW_args`); the per-piece AArch64 lemmas
  `keep_chkHead15` .. `keep_ldStep15` have no x86-64 counterpart (`keepA_pro`).
- `chB_keep5` and `thE_slot` are new: the blocks' prefix lemmas (AArch64: `keep_blk8`, `keep_blk` at the call).
-/
import Spike.Lib.X64HelloProArgs

namespace Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Place WordPlace placeVal ValRep)
open Spike.Lib (Region)
open Spike.Lib.X64
open Spike.Lib.X64WakeMainW (M1 placeVal_cell placeVal_reg)
open Spike.Lib.X64Consumer (Placed Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64HelloSplit (wcP)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (kidH cS2)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words thrJE thrJ cN childN childJ cBlk chB oC)
open Spike.Lib.X64.Flow (XProW)
open Spike.Lib.X64.Flow.Worker (NodeZA)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {w : Words} {w0 w1 w2 w3 w4 : TermRun.Word}

/-! ## The places -/

/-- The stub's registers: packet words `0 .. 4` in `%r12`, `%r13`, `%r14`, `%r15`, `%r9`. -/
def stR : Nat → Reg64
  | 0 => .r12 | 1 => .r13 | 2 => .r14 | 3 => .r15 | _ => .r9

/-- The thread worker's entry registers: packet words `0 .. 4` in `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`. -/
def thR : Nat → Reg64
  | 0 => .rdi | 1 => .rdx | 2 => .rcx | 3 => .r8 | _ => .r9

/-- The thread worker's frame cells: packet word `0` at `−16`, word `i ≥ 1` at `−24 − 8i`. -/
def slK : Nat → Int
  | 0 => -16 | 1 => -32 | 2 => -40 | 3 => -48 | _ => -56

/-- **`kidH` placed at no frame** from each packet word's place holding its machine word. -/
theorem placedSE_kidH_at {s : State} (T : Ty) (hv0 : ValRep lbl w0.val w.w0.toNat)
    (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat) (hv : ValRep lbl w3.val w.w4.toNat)
    (hvu : ValRep lbl w4.val w.w5.toNat) (P : Nat → Place M1.I.RegId)
    (hP : ∀ i, placeVal M1 s (P i) = some (wv w i).toNat) :
    PlacedSE Λ lbl s (kidH T w0 w1 w2 w3 w4) [] :=
  placedSE_nil (placed_kidH T (A := fun _ => True) (fun _ _ => trivial)
    (pkRep_of (P := P) hv0 hv1 hv2 hv hvu fun i _ => hP i))

/-! ## The blocks -/

section Blk

/-- The abstract run's simp set over concrete blocks (as in `X64WakePlacedZ`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-- **The stub's call prefixes keep `%r12`, `%r13`, `%r14`, `%r15`, `%r9`** (the moves write `%rdi .. %r8`). -/
theorem chB_keep5 (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < chB.length) (i : Nat) :
    (arun l (chB.take k) ⟨pc, oC, σ⟩).σ.regs.get64 (stR i) = σ.regs.get64 (stR i) := by
  simp only [chB] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases i with _ | _ | _ | _ | i <;> simp only [stR] <;>
    rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **`scc_rt_thr_worker`'s `.entry` prefixes keep the cells** (six loads before the call). -/
theorem thE_slot (l : String → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < HThrHead.thE.length) :
    (arun l (HThrHead.thE.take k) ⟨pc, HThrHead.oI, σ⟩).σ.slot = σ.slot := by
  simp only [HThrHead.thE] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|_|_|k <;> (try omega) <;> arun_simp

end Blk

/-! ## A prologue keeps `ArgR`'s registers -/

/-- One of `%rdi`, `%rdx`, `%rcx`, `%r8`, `%r9`: `ProArgs.ArgR` (kept as a name for this file's prologue lemma). -/
abbrev R15 (r : Reg64) : Prop := ArgR r

/-- **A prologue's states inside `W`** from its entry's, agreeing on `ArgR`'s registers: `ProArgs`'
`xProW_args`. -/
theorem proW_x15 {W : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {z2 : Nat}
    {J : AS → Ctl → Prop}
    (hW : ∀ σ c, J σ c → ∀ s : State, (∀ r, R15 r → s.st.1.regs.get64 r = σ.regs.get64 r) → W s c) :
    XProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L 5 9 3 z2 4 Wk.wcPs J :=
  xProW_args hW

/-! ## `ZObl`'s fields -/

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {ms : List TermRun.Frame → MemSide isa} {R : Region}
  {F : MachineData → Prop} {tp sp0 : BitVec 64} {T : Ty}
  (hv0 : ValRep lbl w0.val w.w0.toNat) (hv1 : ValRep lbl w1.val w.w2.toNat) (hv2 : ValRep lbl w2.val w.w3.toNat)
  (hv : ValRep lbl w3.val w.w4.toNat) (hvu : ValRep lbl w4.val w.w5.toNat)

/-- `childJ`'s packet words at `stR`'s registers. -/
theorem childJ_stR {cW : Ctl} {σ : AS} {c : Ctl} (hJ : childJ cW w tp sp0 σ c) (i : Nat) :
    σ.regs.get64 (stR i) = wv w i := by
  obtain ⟨-, h12, -, h13, h14, h15, h9, -⟩ := hJ
  rcases i with _ | _ | _ | _ | i <;>
    first | exact h12 | exact h13 | exact h14 | exact h15 | exact h9

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hZc`: the stub placed** (the source at `kidH`): packet words in `%r12 .. %r15`, `%r9` (`childJ`),
which the `testq`, the `je`, the `xorl` and the call block's moves into `%rdi .. %r8` keep. -/
theorem zc_placed : ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (cN (_root_.Executable.labels exe).label (kidH T w0 w1 w2 w3 w4) w tp sp0 i) (cBlk i) := by
  have one : ∀ {blk : List (Directive × Nat)}, blk.length = 1 → ∀ {k : Nat}, k < blk.length →
      ∀ (σ : AS) (c : Ctl) (pc : Int64) (m : MachineData),
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, oC, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, oC, σ⟩).σ →
      childJ (kidH T w0 w1 w2 w3 w4) w tp sp0 σ c → ∀ s' : State, s'.st.1 = m →
      PlacedSE Λ lbl s' c [] := by
    intro blk hb k hk σ c pc m hA' hJ s' hs
    obtain rfl : k = 0 := by omega
    obtain rfl := hJ.1
    refine placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.r (stR i))) fun i => ?_
    rw [placeVal_reg, hs, hA'.regs]
    exact congrArg _ (congrArg _ (childJ_stR hJ i))
  intro i
  cases i
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ.1 _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ.1 _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    exact ⟨one rfl hk σ c _ m hA' hJ _ rfl, fun _ h => h⟩
  · intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
    obtain ⟨hJ, -⟩ := hJ
    obtain rfl := hJ.1
    refine ⟨placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.r (stR i))) fun i => ?_, fun _ h => h⟩
    rw [placeVal_reg]
    show some (m.regs.get64 (stR i)).toNat = _
    rw [hA'.regs]
    erw [chB_keep5 (_root_.Executable.labels exe).label _ σ hk i]
    exact congrArg _ (congrArg _ (childJ_stR hJ i))

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hzT`: the thread worker's prologue placed** (the source at `kidH`): packet words in `%rdi`,
`%rdx .. %r9` (`thrJE`), which the prologue keeps (`proW_x15`). -/
theorem zT_placed : XProW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F (ms [])
    ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs
    (thrJE (kidH T w0 w1 w2 w3 w4) w tp sp0) :=
  proW_x15 fun σ c hJ s hx => by
    obtain ⟨rfl, h0, -, h2, h3, h4, h5, -⟩ := hJ
    refine placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .reg (.r (thR i))) fun i => ?_
    rw [placeVal_reg]
    rcases i with _ | _ | _ | _ | i
    · erw [hx .rdi (.inl rfl)]; exact congrArg _ (congrArg _ h0)
    · erw [hx .rdx (.inr (.inl rfl))]; exact congrArg _ (congrArg _ h2)
    · erw [hx .rcx (.inr (.inr (.inl rfl)))]; exact congrArg _ (congrArg _ h3)
    · erw [hx .r8 (.inr (.inr (.inr (.inl rfl))))]; exact congrArg _ (congrArg _ h4)
    · erw [hx .r9 (.inr (.inr (.inr (.inr rfl))))]; exact congrArg _ (congrArg _ h5)

include hv0 hv1 hv2 hv hvu in
/-- **`ZObl.hZEt`: the thread worker's head placed** (the source at `kidH`): packet words in the frame's cells
`−16`, `−32 .. −56` (`thrJ`), which the head's loads into `%rdi .. %r9` keep; the cells in the region (`hlo`,
`hhi`). -/
theorem zEt_placed (hlo : R.lo ≤ -56) (hhi : -8 ≤ R.hi) : NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (HThrHead.tN (_root_.Executable.labels exe).label (thrJ (kidH T w0 w1 w2 w3 w4) w tp sp0)
      (fun _ c => c = wcP w0 w1 w2 w3 w4) .e) HThrHead.thE := by
  intro s σ c _ _ _ _ _ _ hJ k hk m hA' _
  obtain ⟨rfl, h16, -, h32, h40, h48, h56, -⟩ := hJ
  refine ⟨placedSE_kidH_at T hv0 hv1 hv2 hv hvu (fun i => .slot (R.addr (slK i)).toNat) fun i => ?_, fun _ h => h⟩
  have hs := thE_slot (_root_.Executable.labels exe).label (_root_.Executable.labels exe |>.label
    ".Lscc_rt_thr_worker.entry") σ hk
  rcases i with _ | _ | _ | _ | i
  · erw [placeVal_cell hA' (show R.Off (-16) from ⟨by decide, by omega, by omega⟩) _ rfl, hs, h16]; rfl
  · erw [placeVal_cell hA' (show R.Off (-32) from ⟨by decide, by omega, by omega⟩) _ rfl, hs, h32]; rfl
  · erw [placeVal_cell hA' (show R.Off (-40) from ⟨by decide, by omega, by omega⟩) _ rfl, hs, h40]; rfl
  · erw [placeVal_cell hA' (show R.Off (-48) from ⟨by decide, by omega, by omega⟩) _ rfl, hs, h48]; rfl
  · erw [placeVal_cell hA' (show R.Off (-56) from ⟨by decide, hlo, by omega⟩) _ rfl, hs, h56]; rfl

/-- **`ZObl.hZT`: the thread worker's tail placed** (the source at `cS2`, reading nothing). -/
theorem zTT_placed : ∀ i, NodeZA (fun s c => PlacedSE Λ lbl s c []) exe endPc R F
    (HThrTail.NA (_root_.Executable.labels exe).label (cS2 w0 w1 w2 w3 w4) tp sp0 i) (HThrTail.blkN i) := by
  intro i
  cases i <;> intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _ <;>
    first | obtain ⟨rfl, -⟩ := hJ | obtain rfl := hJ
  all_goals exact ⟨placedSE_nil placed_cS2, fun _ h => h⟩

end Nodes

end Spike.Lib.X64.Flow.Worker.Hello.PlacedZ

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zc_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zc_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zT_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zT_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zEt_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zEt_placed

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zTT_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zTT_placed
