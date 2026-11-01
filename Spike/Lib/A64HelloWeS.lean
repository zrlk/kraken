/-
**hello.w's state at `wc_rodata`'s entry after `bl wc_rodata` inside the start's level** (AArch64;
`StartWcS.hello_start_wc_segWS`'s `hWe`, `StartH0U.hst0_ofHU_i0`'s `hWe`): a state at `Hello1.mNC`
(`wc_rodata`'s entry, `scc_rt_main`'s frame at `-80` of the region `R`, the source still at the start's control
`c0`) is inside `StartWf.WSH`.

The state is the first of `wc_rodata`'s prologue head in the callee's region `Hello1.mR R` (`at_enter`), so it is
`RdWfSF.proW_rdWSHF`'s first block at its first instruction (`blkW_at0`) at the entry invariant `rdJe` (the
caller's state at `mNC` entered at `-80`), whose controls are `c0`, placed at every state (`hpl0`, `proW_ofCtl`).

- `proW_ofCtl`: a prologue inside a predicate its invariant's controls satisfy at every state (`OfCtl.proW_ofCtl`).
- `blkW_at0`: a block node's state at its first instruction.
- `rdJe`: `wc_rodata`'s entry invariant at a caller's state at `mNC`.
- `hWe_W0SH`: `mNC`'s states inside `WSH` (generic in the region, the frame condition and the entry invariant).
- `hWe_WS`: the same at `StartWcS.WS … []`, `hello_start_wc_segWS`'s `hWe` form.
-/
import Spike.Lib.A64HelloRdWfSF
import Spike.Lib.A64HelloStartWcS
import Spike.Lib.A64HelloOfCtl

namespace Spike.Lib.A64.HelloPh.WeS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ProW)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.HelloPh.WcW (freeNH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.Hello1 (mNC mR mF)
open Spike.Lib (Arena FragS Frag Ctl Region)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## Generic node facts -/

section Gen

variable {W : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A prologue is inside a predicate its invariant's controls satisfy at every state** (`h`), with no outside
moves; `OfCtl.proW_ofCtl`. -/
theorem proW_ofCtl {ms : Spike.Lib.MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : FAS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, W s c) :
    ProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  Spike.Lib.A64.HelloPh.OfCtl.proW_ofCtl h

/-- **A block node's state at its first instruction is inside `W`** (`BlkW` at `0`, the block nonempty). -/
theorem blkW_at0 {K : State → State → Prop} {n : ND} {blk : List Directive} (hW : BlkW W K exe endPc R F n blk)
    (hl : 0 < blk.length) {s : State} {c : Ctl} (h : At exe endPc R F n s c) : W s c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  have := (hW s σ c he hn hd hpc hA hF hJ 0 hl s.st.1 hA (Spike.Lib.A64.Flow.DFrame.refl _ _)).1
  rw [Spike.Lib.A64.Flow.ofNat4_zero, ← hpc] at this
  exact this

end Gen

/-- A memory side for the prologue's first block, which does not read it (`ProW.w0`). -/
def msT : Spike.Lib.MemSide isaLSE2 :=
  ⟨fun _ => False, fun _ => False, none, fun _ _ => False, 0, 0, fun _ _ => 0, fun _ _ => 0, 0, fun _ => [],
    fun _ _ => False, fun _ => False, fun _ _ => False, fun _ _ _ _ _ => False, fun _ _ _ _ => False,
    fun _ _ => False, fun _ => True, False, False⟩

/-- **`wc_rodata`'s entry invariant at a caller's state at `mNC`**: the caller's state `σC` at `mNC` (invariant
`J`) at the control `c`, entered at `-80` (`at_enter`'s node invariant). -/
def rdJe (lab : Label → Int64) (J : FAS → Ctl → Prop) (c : Ctl) (σC : FAS) (σ : FAS) (c' : Ctl) : Prop :=
  c' = c ∧ σ = Spike.Lib.A64.Flow.enter (-80) σC ∧ (mNC lab J).J σC c

section Hello

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])

include hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0

/-- **`mNC`'s states inside `WSH`** (`hello_start_wc_segWS`'s `hWe`): at `wc_rodata`'s entry after
`bl wc_rodata` in a region `R` holding `wc_rodata`'s frame below `scc_rt_main`'s (`hRlo`), every control of the
entry invariant `J` is the start's `c0` at the thread pointer `tp` (`hJ`), the limit word `limA tp` mapped
(`hmr`) and unmapped in private memory under `F` (`hun`). -/
theorem hWe_W0SH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab J) s c → WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  intro s c h
  obtain ⟨m0, σC, hA⟩ := Spike.Lib.A64.Flow.at_enter (lo' := -208) (hi' := 0)
    (show R.lo ≤ (mNC L.lab J).o.sp + -208 by simp only [mNC]; omega)
    (show (mNC L.lab J).o.sp < R.hi by simp only [mNC]; omega) (Int.le_refl 0)
    (show (mNC L.lab J).o.sp % 8 = 0 by simp only [mNC]; decide) h
  obtain ⟨hmR, halR, -⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok (F := fun _ => True) hR hal (fun _ _ _ _ => trivial)
    hRlo hhi m0 σC
  have hctl : ∀ σ c', rdJe L.lab J c σC σ c' → c' = c0 := by
    rintro σ c' ⟨rfl, -, ⟨σe, hJe, -⟩, -⟩
    exact (hJ σe c' hJe).1
  have hpro := Spike.Lib.A64.HelloPh.RdWfSF.proW_rdWSHF (fs := []) (a := a) (rS := ⟨0, 0⟩) (ar := ar) (p := p)
    (Dt := Dt) (Ctx := Ctx) (lsize := lsize) (frM := frM) (lbl := lbl) (ms := msT)
    (F := mF R F m0 σC) hp hlo hΛ hlab hsite hcl hX0 (.inl rfl) hmR halR
    (by simp only [mR, Region.callee]; omega) (by simp only [mR, Region.callee]; omega)
    (J0 := rdJe L.lab J c σC) (tp := tp)
    (by
      rintro σ c' ⟨-, rfl, ⟨σe, hJe, -, -, -, -, ht⟩, -⟩
      exact ht.trans (hJ σe c hJe).2)
    hmr (fun m hm => hun m hm.1)
    (fun σ c' h => by rw [hctl σ c' h]; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (proW_ofCtl fun σ c' h s => by rw [hctl σ c' h]; exact hpl0 s)
  exact blkW_at0 hpro.w0 (by decide) hA

/-- **`hWe_W0SH` at the start's level with frames** (`StartWcS.WS … []`, `hello_start_wc_segWS`'s `hWe` form). -/
theorem hWe_WS (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.TPIDR_EL0 = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false ⟨Spike.Lib.A64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab J) s c →
      Spike.Lib.A64.HelloPh.StartWcS.WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c [] :=
  hWe_W0SH hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0 hR hal hRlo hhi hJ hmr hun

end Hello

end Spike.Lib.A64.HelloPh.WeS

/-- info: 'Spike.Lib.A64.HelloPh.WeS.hWe_W0SH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeS.hWe_W0SH

/-- info: 'Spike.Lib.A64.HelloPh.WeS.hWe_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeS.hWe_WS
