/-
**An output call, assembled with the frames placed knowing the block**
(x86-64; the twin of `Spike/Lib/LowerA64/PrintCallInstJ.lean`):
`printCallC_inst`, `printCallCH_inst` (`Spike/Lib/LowerX64/PrintCallInst.lean`)
with the per-call `hPer`, `hPerE` split. The suspended frames are asked only
at the argument block's four pieces' states (`hfpJ`, for every block `B` of
the call and any source control `cT` at the call node, through
`printArgWE_w2'`), not under the caller's whole frame condition; the
caller's continuation free of `ZBad` is one premise over the source
(`hNoS`); what stays per call is `PrintCallOkR` at the call states
(`hcall`, `hcallE`); the write tail at `print`'s system-call states is one
premise whatever the call (`hDtP`).

- `printWE_w2J`, `printW_w2J`, `printW_w2BJ`: `printWE_w2'`, `printW_w2'`,
  `printW_w2B'` with the frames placed knowing the block (`hfpJ`), no
  `FStable` of the caller's frame condition;
- `printW_hPWJ_ABJ`, `printWE_hPWEJ_J`: `printCallC_of'`'s `hPW`, `hPWE`
  inside `W2` from `hNoS`, `hfpJ`, `hcall`/`hcallE` (and `hDtP`);
- `printCallC_instJ`: at `PrintCallC`;
- `printCallCH_instJ`: at `PrintCallCH`.
-/
import Spike.Lib.LowerX64.PrintCallInst

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Lower.InvX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange lbl_lt32 printTop0)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC printLD)
open Spike.Lib.PrintSvc (printTop_ext self_mem_printTerms)
open Spike.Lib.X64.PrintA (PrintAW)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.LowerShape (printInsts)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **`printWE_w2'` with the frames placed knowing the block**
(`printArgWE_w2'`): the suspended frames asked only at the argument block's
four pieces' states (`hfpJ`, for every block `B` of the call), not under
the caller's whole frame condition, so no `FStable` of it. -/
theorem printWE_w2J {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {envR : TermRun.Env} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = ⟨.ret .unit, envR, none⟩)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B Jn)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hfr : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) :
    PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F fr Cd Bl kk pc n b o m cw Jn ⟨.ret .unit, envR, none⟩ := by
  have hfE : FrOk2 ⟨.ret .unit, envR, none⟩ (printFrame x e c1 :: fs) := frOk2_ret he hfs
  intro B hB
  have hA : PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs))
      K exe endPc R F fr B Jn := printArgWE_w2' hI hpr habI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hp hCd hBl hB
    (fun σ c h => .inr (by rw [hJn σ c h]; rfl)) (hfpJ B hB)
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfE⟩)
  refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  intro σC c hc F' hJF
  have hk := hcall B hB σC c hc
  refine printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
    (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
    hp (fun _ c h => h.elim (fun h => h ▸ hfE) False.elim) ?_
  exact PrintAW.ofJF hJF.1 fun _ c' s h hF =>
    .of_ext (.inr (h.elim (fun h => by rw [h]; rfl) False.elim))
      (hfr B hB σC c hc F' hJF s hF).choose_spec.toFramesPlaced

/-- **`printW_w2'` with the frames placed knowing the block**
(`printArgWE_w2'`): the suspended frames asked only at the argument block's
four pieces' states (`hfpJ`, for every block `B` of the call), so no
`FStable` of the caller's frame condition. -/
theorem printW_w2J {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B Jn)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hfr : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    {ms : MemSide isa}
    (hDt : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      Dt s)
    (hms : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      (σC.regs.get64 .rsi).toNat = printN nv mv →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      (∀ k j, k + j < printN nv mv →
        ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC pw wn mv (k + j))
          (fun c0 => ∃ mw b, c0 = nextC pw wn mv (k + j) mw b)) ∧
      ∀ k c1, PrintC pw wn nv mv k c1 → ms.we s c1) :
    PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F ms fr Cd Bl kk pc n b o m cw Jn pw wn nv mv := by
  have hfT := frOk2_printTop0 (fs := fs) (pw := pw) (wn := wn) (mv := mv) (x := x) (c1 := c1) he hfs
  have hfP : ∀ j c, PrintC pw wn nv mv j c ∨ PrintC pw wn nv mv j c → FrOk2 c (printFrame x e c1 :: fs) :=
    fun _ _ h => h.elim (fun h => frOk2_printC h he hfs) fun h => frOk2_printC h he hfs
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  intro B hB
  have hA : PrintArgW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs))
      K exe endPc R F fr B Jn := printArgWE_w2' hI hpr habI hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hCd hBl hB
    (fun σ c h => by rw [hJn σ c h]; exact printTop_ext (self_mem_printTerms _)) (hfpJ B hB)
    (fun σ c h => ⟨fun h' => absurd h' (List.cons_ne_nil _ _), (hJn σ c h) ▸ hfT⟩)
  refine ⟨⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩, ?_⟩
  · intro σC c hc F' hJF
    have hk := hcall B hB σC c hc
    exact printW2 hI hpr habI hph hk.ok hk.al hk.lo hk.hi hk.lo8 hk.hi8 hsub hfit
      (fun md h => hk.off md (hJF.2 md h).1) hk.len hk.raPh hk.raAb
      hp hfP (printAW_placedSE hJF.1 (fun j c h => h.elim printC_top printC_top) (hfr B hB σC c hc F' hJF))
  · intro σC c hc hN F' hJF s c' hAt
    obtain ⟨j, hj, -⟩ := printSys_src hAt hN
    have hlo2 : R.lo ≤ (-(fr.size : Int) - 8 - 8) + -40 := by omega
    have hkb : (-(fr.size : Int) - 8 - 8) + 16 ≤ R.hi := by omega
    have hk16 : (-(fr.size : Int) - 8 - 8) % 16 = 0 := by omega
    have hw := printSvc_w2 (kb := -(fr.size : Int) - 8 - 8) (F' := F') (Λ := Λ) (p := p) (rd := rd) (G := G)
      (ar := ar) (J := J) (lsize := lsize) hI hpr habI hph hR hal hl hh hlo2 hkb hk16 hsub hFO
      (fun md h => (hJF.2 md h).1) hN hp
      (hfP j c' (.inl hj)) (printSvc_placedSE hAt hN (hfr B hB σC c hc F' hJF))
      (hDt B hB σC c hc F' hJF) hAt
    rw [hI.labOk] at hw
    exact ⟨hw, hms B hB σC c hc hN F' hJF s c' hAt⟩

/-- **`printW_w2B'` with the frames placed knowing the block**
(`printW_w2J`). -/
theorem printW_w2BJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfpJ : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B Jn)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hfr : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' →
      ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    {ms : MemSide isa}
    (hDt : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr Jn) σC F' → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      Dt s)
    (hbo : ms.bo = ByteOut p lbl) (hwe : ms.we = WeAb abi (Ab lab))
    (hpw : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat)
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F ms fr Cd Bl kk pc n b o m cw Jn pw wn nv mv := by
  refine printW_w2J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hJn he hfs hfpJ
    hcall hfr hDt ?_
  intro B hB σC c hc hN F' hF' s c' hAt
  have hk := hcall B hB σC c hc
  obtain ⟨l, hpw', hlb⟩ := hpw B hB σC c hc
  have h32 := lbl_lt32 hrg hb32 hlb
  have hlen := hk.len
  refine ⟨fun k j hkj => ?_, fun k c2 _ => ?_⟩
  · rw [hbo]
    exact Spike.Lib.X64.byteOut_at hpw' hlb (by omega) hkj
  · rw [hwe]
    have hlo2 : (pR (-(fr.size : Int) - 8 - 8) R).lo ≤ -16 := by have := hk.lo; omega
    have hhi2 : -8 ≤ (pR (-(fr.size : Int) - 8 - 8) R).hi := by have := hk.hi; omega
    have hw := Spike.Lib.X64.PrintG.printSvcWe hI hpr hph hlo2 hhi2 hlen hAt
    rw [hI.labOk] at hw
    exact hw

/-- **`printCallC_of'`'s `hPW` inside `W2`, the frames placed knowing the
block** (`printW_w2BJ` at `printJ`): `printW_hPWJ_AB` with the per-call
`hPer` split into the continuation free of `ZBad` (`hNoS`), the frames
along the argument block (`hfpJ`, at any source control `cT` at the call
node), the residual `PrintCallOkR` (`hcall`) and the write tail at
`print`'s system-call states, whatever the call (`hDtP`). -/
theorem printW_hPWJ_ABJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw hS
  exact printW_w2BJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs
    (hfpJ c0 pc env lits cs bufs n x is a e b o m cw c1 _ kk kk' pc' hG0 hT hi)
    (hcall c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn mv kk kk' pc' hG0 hT hi)
    (framesPlaced_printFJ hf hlo hhi hS hFP) (fun _ _ _ _ _ _ _ s c' hAt => hDtP _ _ _ _ _ _ s c' hAt) rfl rfl hpw
    hrg hb32

/-- **`printCallC_of'`'s `hPWE` inside `W2`, the frames placed knowing the
block** (`printWE_w2J` at `printJ` at `print`'s `ret ()`): `printWE_hPWEJ`
with the per-call `hPerE` split into the continuation free of `ZBad`
(`hNoS`), the frames along the argument block (`hfpJ`) and the residual
`PrintCallOkR` (`hcallE`). -/
theorem printWE_hPWEJ_J {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT))
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩ := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi hS
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  exact printWE_w2J hI hpr habI hph hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs
    (hfpJ c0 pc env lits cs bufs n x is a e b o m cw c1 _ kk kk' pc' hG0 hT hi)
    (hcallE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi)
    (framesPlaced_printFJ hf hlo hhi hS hFP)

/-- **An output call at `PrintCallC`, assembled with the frames placed
knowing the block** (`printCallC_of'` as `printCallC_inst`, its `hPW`,
`hPWE` by `printW_hPWJ_ABJ`, `printWE_hPWEJ_J`): the per-call `hPer`,
`hPerE` split into the continuation free of `ZBad` (`hNoS`), the frames
along the argument block (`hfpJ`), the residual `PrintCallOkR` (`hcall`,
`hcallE`) and `print`'s system-call states detached (`hDtP`). -/
theorem printCallC_instJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_of' hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_ABJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hfpJ hcall hDtP)
    (printWE_hPWEJ_J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hfs hFP fp ra tp hNoS
      hfpJ hcallE)
    hAb

/-- **An output call at `PrintCallCH`, assembled with the frames placed
knowing the block** (`printCallCH_ofR` as `printCallCH_inst`; the premises
of `printCallC_instJ`). -/
theorem printCallCH_instJ {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hfpJ : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (cT : Ctl)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F fr B (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          cT))
    (hcall : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hcallE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩)).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_ofR hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWJ_ABJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hfpJ hcall hDtP)
    (printWE_hPWEJ_J hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hfs hFP fp ra tp hNoS
      hfpJ hcallE)
    hAb

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.printWE_w2J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_w2J

/-- info: 'Spike.Lib.LowerX64.printW_w2J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2J

/-- info: 'Spike.Lib.LowerX64.printW_w2BJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2BJ

/-- info: 'Spike.Lib.LowerX64.printW_hPWJ_ABJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPWJ_ABJ

/-- info: 'Spike.Lib.LowerX64.printWE_hPWEJ_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_hPWEJ_J

/-- info: 'Spike.Lib.LowerX64.printCallC_instJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_instJ

/-- info: 'Spike.Lib.LowerX64.printCallCH_instJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_instJ
