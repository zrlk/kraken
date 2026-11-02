/-
**hello.w on x86-64: the state at `wc_rodata`'s entry after `call wc_rodata` inside the start's level** (the twin
of `Spike/Lib/A64HelloWeS.lean`): a state at `Hello1.mNC` (`wc_rodata`'s entry, `scc_rt_main`'s frame at `-80` of
the region `R`, the source still at the start's control `c0`) is inside `StartWf.WSH`.

The state is the first of `wc_rodata`'s prologue head in the callee's region `Hello1.mR R` (`at_enter`), so it is
`RdWfSF.proW_rdWSHF`'s first block at its first instruction (`blkW_at0`) at the entry invariant `rdJe` (the
caller's state at `mNC` entered at `-80`), whose controls are `c0`, placed at every state (`hpl0`, `proW_ofCtl`).

- `proW_ofCtl`: a prologue inside a predicate its invariant's controls satisfy at every state (`OfCtl.proW_ofCtl`).
- `blkW_at0`: a block node's state at its first instruction.
- `msT`: a memory side for the prologue's first block, which does not read it.
- `rdJe`: `wc_rodata`'s entry invariant at a caller's state at `mNC`.
- `hWe_W0SH`: `mNC`'s states inside `WSH` (generic in the region, the frame condition and the entry invariant).
- `hWe_WS`: the same at `StartWcS.WS … []`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The prologue is x86-64's five-node `XProW` (`wc_rodata`'s frame of 32, `.Lwc_rodata.stk`), so `proW_ofCtl`
  takes its byte sizes and saved registers (AArch64: `ProW` with `XReg` pairs).
- A block's instructions are cells with sizes: `blkW_at0` is at `cellOff blk 0 = 0` (AArch64: `4 * 0`).
- `mNC` takes the region `R` (it records `%rbp = R.addr (-8)`); `call` pushes the return address, so the callee
  region is `R.callee (-80) (-208) 8` and `R.hi` is at least `8` (AArch64: `0`); there is no 16-alignment
  premise. The thread pointer is `fsBase` (AArch64: `TPIDR_EL0`).
-/
import Spike.Lib.X64HelloRdWfSF
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloOfCtl

namespace Spike.Lib.X64.HelloPh.WeS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (ND BlkW NodeW At)
open Spike.Lib.X64.Flow (XProW)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib.X64.HelloPh.StartWf (WSH)
open Spike.Lib.X64.Flow.Hello1 (mNC mR mF)
open Spike.Lib (Arena FragS Frag Ctl Region)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## Generic node facts -/

section Gen

variable {W : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A prologue is inside a predicate its invariant's controls satisfy at every state** (`h`), with no outside
moves; `OfCtl.proW_ofCtl`. -/
theorem proW_ofCtl {ms : Spike.Lib.MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : FAS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, W s c) :
    XProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  Spike.Lib.X64.HelloPh.OfCtl.proW_ofCtl h

/-- **A block node's state at its first instruction is inside `W`** (`BlkW` at `0`, the block nonempty). -/
theorem blkW_at0 {K : State → State → Prop} {n : ND} {blk : List (Directive × Nat)}
    (hW : BlkW W K exe endPc R F n blk) (hl : 0 < blk.length) {s : State} {c : Ctl}
    (h : At exe endPc R F n s c) : W s c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  have := (hW s σ c he hn hd hpc hA hF hJ 0 hl s.st.1 hA (Spike.Lib.X64.DFrame.refl _ _)).1
  rw [show Spike.Lib.X64.cellOff blk 0 = 0 from rfl, Spike.Lib.X64.Flow.ofNat_zero', ← hpc] at this
  exact this

end Gen

/-- A memory side for the prologue's first block, which does not read it (`XProW.w0`). -/
def msT : Spike.Lib.MemSide isa :=
  { rd := fun _ => False, rt := fun _ => False, K := none, G := fun _ _ => False, heap := 0, ctr := 0,
    units := fun _ _ => 0, off := fun _ _ => 0, cells := 0 }

/-- **`wc_rodata`'s entry invariant at a caller's state at `mNC`**: the caller's state `σC` at `mNC` (region `R`,
invariant `J`) at the control `c`, entered at `-80` (`at_enter`'s node invariant). -/
def rdJe (lab : Label → Int64) (R : Region) (J : FAS → Ctl → Prop) (c : Ctl) (σC : FAS) (σ : FAS) (c' : Ctl) :
    Prop :=
  c' = c ∧ σ = Spike.Lib.X64.enter (-80) σC ∧ (mNC lab R J).J σC c

section Hello

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])

include hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0

/-- **`mNC`'s states inside `WSH`**: at `wc_rodata`'s entry after `call wc_rodata` in a region `R` holding
`wc_rodata`'s frame below `scc_rt_main`'s (`hRlo`, `hhi`), every control of the entry invariant `J` is the
start's `c0` at the thread pointer `tp` (`hJ`), the limit word `limA tp` mapped (`hmr`) and unmapped in private
memory under `F` (`hun`). -/
theorem hWe_W0SH (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab R J) s c → WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  intro s c h
  obtain ⟨m0, σC, hA⟩ := Spike.Lib.X64.at_enter (e0 := 0) (lo' := -208) (hi' := 8)
    (show R.lo ≤ (mNC L.lab R J).o.sp - 0 + -208 by simp only [mNC]; omega)
    (show (mNC L.lab R J).o.sp - 0 + 8 ≤ R.hi by simp only [mNC]; omega)
    (show ((mNC L.lab R J).o.sp - 0) % 8 = 0 by simp only [mNC]; decide) h
  have hmR : (mR R).OK := Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hctl : ∀ σ c', rdJe L.lab R J c σC σ c' → c' = c0 := by
    rintro σ c' ⟨rfl, -, σe, hJe, -⟩
    exact (hJ σe c' hJe).1
  have hpro := Spike.Lib.X64.HelloPh.RdWfSF.proW_rdWSHF (fs := []) (a := a) (rS := ⟨0, 0⟩) (ar := ar) (p := p)
    (Dt := Dt) (Ctx := Ctx) (lsize := lsize) (frM := frM) (lbl := lbl) (ms := msT)
    (F := mF R F m0 σC) hp hlo hΛ hlab hsite hcl hX0 (.inl rfl) hmR
    (by simp only [mR, Region.callee]; omega) (by simp only [mR, Region.callee]; omega)
    (J0 := rdJe L.lab R J c σC) (tp := tp)
    (by
      rintro σ c' ⟨-, rfl, σe, hJe, -, -, -, -, ht, -, -⟩
      exact ht.trans (hJ σe c hJe).2)
    hmr (fun m hm => hun m hm.1)
    (fun σ c' h => by rw [hctl σ c' h]; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (proW_ofCtl fun σ c' h s => by rw [hctl σ c' h]; exact hpl0 s)
  exact blkW_at0 hpro.w0 (by decide) hA

/-- **`hWe_W0SH` at the start's level with frames** (`StartWcS.WS … []`). -/
theorem hWe_WS (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab R J) s c →
      Spike.Lib.X64.HelloPh.StartWcS.WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [] :=
  hWe_W0SH hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0 hR hRlo hhi hJ hmr hun

end Hello

end Spike.Lib.X64.HelloPh.WeS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WeS.hWe_W0SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeS.hWe_W0SH

/-- info: 'Spike.Lib.X64.HelloPh.WeS.hWe_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeS.hWe_WS
