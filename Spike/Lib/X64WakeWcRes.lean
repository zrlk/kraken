/-
**wake.w's `wc_main` from the box's store to `.x19`: the reserve**
(x86-64; twin of `Spike/Lib/A64WakeWcRes.lean`), inside `W`, in any valid
layout of `wakeCells` (`Spike/Lib/X64WakeCode.lean`), from checks decided
once on the cells (`decide +kernel`):

    .Lwc_main.x18 + 18:                 -- past the box's store (`bX l A`)
      call scc_rt_thread_reserve        -- (resB), `.x19` pushed at -72
    .Lwc_main.x19:                      -- %rax = n + 1 = 1

The reserve is `Rt.Reserve`'s segment at the counter's old value `0`
(`ResOkA`: owned at the `lock xadd` node's states, not at every state at its
pc), the source unchanged across it.

**Where the source's `publish` is matched.** AArch64's segment has a fence
row here (`dmb ishst`, `A64WakeWcRes.dmb_ndW`) at which the source takes its
publication step. wake's x86-64 listing has no instruction at that point
(scc's `# fence st` emits no code under TSO, `X64WakeWcSp0`), so this
segment has no fence node and takes no source step: the source stays at the
landing's control (`boxTerm`, `o` bound to the box's owned locative) through
the reserve (`rX` carries `bX`'s facts and `Q` at the same control), through
`scc_rt_alloc_tcb` (`X64WakeWcSp3Seg`), the tid store and
`scc_rt_thread_init`, all parametric in the source control. Its one
publication step is taken at `wc_main`'s `mfence` at `.Lwc_main.x21 + 12`
(`X64WakeClone.wcNf`, `X64WakeWcPub.wake_wc_clone_pub_segW`): matched once,
there, and nowhere between the box's store and `.x21`.

The segment is stated on any region `R` with `wc_main`'s frame based at the
saved `%rbp` (`WcClone.oW = ⟨-64, [(.rbp, 0)]⟩`, the instance's
`R.fp (-8)`, `X64WakeWcSp0`): the cell at `-16`, the saved `%rdi` at `-8`,
the caller's `%rbp` and return address at `0` and `8`. The reserve's region
is `R.callee (-72) (-40) 8` (`rAR`: its frame of 32 and saved `%rbp` below
the return address at `-72`).

- `resB`, `wcResIn`, `wake_wcResIn`, `wake_reserveIn`: the call block and
  the code checks;
- `bX_slots`: `bX`'s facts depend only on the slots `-16 … 8`;
- `rJ`, `RsN`, `rN`, `rX`, `rNe`, `rAR`, `ResCtx`: the source and frame
  past the store, the nodes (the call block, the reserve's entry), the exit
  at `.x19`, the reserve's entry, region and call context;
- `reserveW_mono`, `WcResW`: the reserve's obligations under a stronger
  frame condition, the nodes' states inside `W`;
- `wake_wc_res_segW`: the segment from the landing past the box's store to
  `.x19`.
-/
import Spike.Lib.X64WakeWcSp0
import Spike.Lib.Rt.X64RtReserveA

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Spike.Lib.X64.Rt.Reserve (ResG RN rvN rvX ResOkA ReserveW reserve_segWA)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section ResMono

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F' : MachineData → Prop}

/-- The reserve's obligations under a weaker frame condition hold under a
stronger one. -/
theorem reserveW_mono {W : Frag isa} {K : State → State → Prop} {q : ResG} {i : RN}
    (h : ReserveW W K exe endPc R F q i) (hFF : ∀ m, F' m → F m) : ReserveW W K exe endPc R F' q i := by
  cases i <;> first | exact Ret0.blkW_mono h hFF | exact Ret0.nodeW_mono h hFF

end ResMono

/-! ## The block and the checks -/

/-- The reserve's call. -/
def resB : List (Directive × Nat) := (parse("call scc_rt_thread_reserve")).zip [5]

block_spec resB (-72) 16 (⟨-64, [(.rbp, 0)]⟩ : SO) resB

/-- **The call in `cells`**: at `.x18`'s `18`, `.x19` right after. -/
def wcResIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.x18" 18 resB && labelGapB cells ".Lwc_main.x18" ".Lwc_main.x19" 23

theorem wake_wcResIn : wcResIn SccCode.wakeCells = true := by decide +kernel

theorem wake_reserveIn : Flow.Reserve.reserveIn SccCode.wakeCells = true := by decide +kernel

/-! ## Nodes -/

/-- **`bX`'s facts depend only on the slots `-16 … 8`.** -/
theorem bX_slots {ms : MemSide isa} {lab : Label → Int64} {J0 : AS → Ctl → Prop} {l : WeakMem.AllocLabel}
    {A : Nat} {σ σ' : AS} {c : Ctl} (h : (bX ms lab J0 l A).J σ c)
    (hs : ∀ k : Int, -16 ≤ k → k ≤ 8 → k % 8 = 0 → σ'.slot k = σ.slot k) : (bX ms lab J0 l A).J σ' c := by
  obtain ⟨q, ⟨σe, hJe, h8, h0, hm8⟩, hA, hc, ho⟩ := h
  refine ⟨q, ⟨σe, hJe, ?_, ?_, ?_⟩, ?_, hc, ho⟩
  · rw [hs 8 (by decide) (by decide) (by decide), h8]
  · rw [hs 0 (by decide) (by decide) (by decide), h0]
  · rw [hs (-8) (by decide) (by decide) (by decide), hm8]
  · rw [hs (-16) (by decide) (by decide) (by decide), hA]

/-- `wc_main`'s nodes from the call block to the reserve's entry. -/
inductive RsN where
  | bl | call

section Res

variable (ms : MemSide isa) (lab : Label → Int64) (R : Region) (J0 : AS → Ctl → Prop)
  (Q : WeakMem.AllocLabel → Nat → Ctl → Prop)

/-- **The source and frame past the box's store**: some fresh label's
landing facts (`bX l A`) with the source at `Q l A`. -/
def rJ (σ : AS) (c : Ctl) : Prop := ∃ l A, (bX ms lab J0 l A).J σ c ∧ Q l A c

/-- **The nodes**: the call block (the landing past the box's store,
`%rbp` at the saved `%rbp`) and the reserve's entry (`.x19` pushed at
`-72`). -/
def rN : RsN → ND
  | .bl => ⟨lab ".Lwc_main.x18" + Int64.ofNat 18, ⟨-64, [(.rbp, 0)]⟩, fun σ c =>
      rJ ms lab J0 Q σ c ∧ σ.regs.get64 .rbp = R.addr 0⟩
  | .call => ⟨lab "scc_rt_thread_reserve", ⟨-72, []⟩, fun σ c => rJ ms lab J0 Q σ c ∧
      σ.regs.get64 .rbp = R.addr 0 ∧ σ.slot (-72) = (lab ".Lwc_main.x19").toBitVec⟩

/-- **The exit at `.x19`**: the reserve's result `1` in `%rax`, the source
and frame kept, `%rbp` at the saved `%rbp`. -/
def rX : Unit → ND
  | () => ⟨lab ".Lwc_main.x19", ⟨-64, []⟩, fun σ c => rJ ms lab J0 Q σ c ∧
      σ.regs.get64 .rbp = R.addr 0 ∧ σ.regs.rax.toBitVec = 1#64⟩

end Res

/-- The reserve's entry for the frame ghosts `g.1` and the control `g.2`, at
the counter's old value `0`. -/
def rNe (lab : Label → Int64) (g : Flow.Ret0.AllocTcb.G × Ctl) : ND := rvN lab ⟨g.1, 0#64, g.2⟩ .e

/-- The reserve's region at the call: based at the pushed return address
(`-72`), its frame of 32 and saved `%rbp` below, the return address above. -/
abbrev rAR (R : Region) : Region := R.callee (-72) (-40) 8

/-- **The reserve's call context in `wc_main`'s region `R`** at the memory
`m`, for the ghosts `g` (`WcCtx`'s form). -/
def ResCtx (lab : Label → Int64) (R : Region) (Jc : AS → Ctl → Prop) (g : Flow.Ret0.AllocTcb.G × Ctl)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨-72, []⟩ mC σC ∧ Jc σC c ∧ (rNe lab g).J (enter (-72) σC) c ∧ CKept R (-72) (-40) 8 mC m

/-- **`wc_main`'s states from the call block to `.x19` inside `W`**, none
moved by `K`: the call block's, and the reserve's in its region (at the
counter's old value `0`, returning to `.x19`). -/
structure WcResW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  bl : BlkW W K exe endPc R F (rN ms (_root_.Executable.labels exe).label R J0 Q .bl) resB
  res : ∀ g : Flow.Ret0.AllocTcb.G × Ctl, g.1.ra = ((_root_.Executable.labels exe).label ".Lwc_main.x19").toBitVec →
    ∀ i, ReserveW W K exe endPc (rAR R)
      (fun m => F m ∧ CallerCells R (-72) (-40) 8 m ∧ ResCtx (_root_.Executable.labels exe).label R
        (rN ms (_root_.Executable.labels exe).label R J0 Q .call).J g m) ⟨g.1, 0#64, g.2⟩ i

/-- From the call block to `.x19` inside the trivial predicate, with no
outside moves. -/
theorem WcResW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcResW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms J0 Q := by
  refine ⟨BlkW.triv, fun _ _ i => ?_⟩
  cases i <;> dsimp only [ReserveW] <;> first | exact BlkW.triv | exact NodeW.triv

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from the box's store to `.x19` is one segment inside `W`**
in any valid layout of `wakeCells`: from the landing past the box's store
(`bX l A` on `R`, some fresh label `l`, the source at `Q l A`) to `.x19`
(`rX`). The reserve runs at the counter's old value `0` (`hres`, the counter
owned at the `lock xadd` node's states in the reserve's region), returning
`1`; the source takes no step (its publication is at `.x21`'s `mfence`, see
the module's docstring). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem wake_wc_res_segW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -112) (hhi : 16 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hW : WcResW W K exe endPc R F ms J0 Q)
    (hres : ∀ g : Flow.Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c)
      (fun s c => ∃ x, At exe endPc R F (rX ms (_root_.Executable.labels exe).label R J0 Q x) s c) := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  obtain ⟨h18, hgap⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e19 : lab ".Lwc_main.x19" = lab ".Lwc_main.x18" + Int64.ofNat 23 := label_labelGapB hp hgap
  refine (fn_segW (N := rN ms lab R J0 Q) (E := rX ms lab R J0 Q) (fun i => ?_) RsN.bl).mono_pre ?_
  rotate_left
  · rintro s c ⟨l, A, h, hQ⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hb⟩ := Hello1.At.reg_addr (r := .rbp) (k := 0) rfl h
    exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨l, A, hJ, hQ⟩, hb⟩
  cases i
  case bl =>
    refine seg_ndW (by simp [resB]) resB_ok hF hR (by omega) hhi (code_field hp hend h18 rfl) hW.bl
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RsN.call, ?_, ?_, ?_⟩⟩
    · simp only [rN]; rw [resB_run]
    · simp only [rN]; rw [resB_run]; rfl
    · simp only [rN] at hJ ⊢
      rw [resB_run]
      obtain ⟨⟨l, A, hX, hQ⟩, hb⟩ := hJ
      refine ⟨⟨l, A, bX_slots hX fun k h1 h2 h3 => ?_, hQ⟩, ?_, ?_⟩
      · have hk : ¬ k = -72 := by omega
        simp only [upd_apply, hk, ↓reduceIte]
      · simpa [Reg64s.set64, Reg64s.get64] using hb
      · rw [e19]
        simp only [upd_apply, ↓reduceIte, Int64.toBitVec_add, BitVec.add_assoc]
        rfl
  case call =>
    refine call_nd_FWK (KC := False) (e0 := 0) (lo' := -40) (hi' := 8) (M := fun _ => True)
      (Ne := rNe lab) (Ex := fun g : Flow.Ret0.AllocTcb.G × Ctl => rvX ⟨g.1, 0#64, g.2⟩)
      hR hF (by show R.lo ≤ -72 - 0 + -40; omega) (by decide) (by show (-72 : Int) - 0 < R.hi; omega)
      (by show (-72 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-72 : Int) - 0) % 8 = 0; decide) (by decide)
      (by decide) (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc g hg hkeep => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, h72⟩, ⟨-, -, -, hra⟩⟩ := hg
        have hr : g.1.ra = (lab ".Lwc_main.x19").toBitVec := by
          rw [← hra, ← h72]; rfl
        exact (reserve_segWA hp hend wake_reserveIn hF' hR' hlo' hhi' hFF ⟨g.1, 0#64, g.2⟩
          (by show (0#64 : BitVec 64).toNat + 1 ≤ 1023; decide) ((hres g).mono hFF)
          fun i => reserveW_mono (hW.res g hr i) fun m h => ⟨hFF m h, hcc m h, hkeep m h⟩).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩)
      (fun _ => rfl) ?_ ?_
    · rintro σC c -
      exact ⟨(⟨σC.regs.rsp.toBitVec, σC.regs.rbp.toBitVec, σC.slot (-72 - 0 + 0)⟩, c), rfl, rfl, rfl, rfl, rfl⟩
    · rintro g ⟨⟩ σC c σx c' σR ⟨⟨l, A, hX, hQ⟩, hb, h72⟩ ⟨hc, -, hfp, hra⟩ ⟨hc', hpost⟩ hreg - - hsl
      have hkeep : ∀ k : Int, -16 ≤ k → k ≤ 8 → k % 8 = 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
        hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, rN]; omega)
      refine .inr ⟨(), ?_, by show SO.le ⟨-64, []⟩ ⟨-72 - 0 + 8, []⟩ = true; decide,
        ⟨l, A, hc' ▸ hc ▸ bX_slots hX hkeep, hc' ▸ hc ▸ hQ⟩, ?_, ?_⟩
      · show lab ".Lwc_main.x19" = Int64.ofBitVec g.1.ra
        rw [← hra]
        show _ = Int64.ofBitVec (σC.slot (-72 - 0 + 0))
        rw [show (-72 : Int) - 0 + 0 = -72 by decide, h72, int64_ofBitVec_toBitVec]
      · rw [← hb]
        simp only [Reg64s.get64]
        rw [hreg, hpost.2.1, ← hfp]; rfl
      · rw [hreg, Rt.Reserve.post_rax hpost]; rfl

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wcResIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wcResIn

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_res_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_res_segW
