/-
**A call of `print` inside `W2` under the labels' byte step and the write
abort's justification** (x86-64; the twin of `Spike/Lib/LowerA64/PrintWBW2.lean`):
`printW_w2` (`Spike/Lib/LowerX64/PrintWEW2.lean`) at a memory side whose byte
step is `print`'s (`ms.bo = ByteOut p lbl`) and whose abort justification is
the write abort's phase (`ms.we = WeAb abi (WriteAb.Ab lab)`), as `msOfAB`
has them (`msOfAB_bo`, `msOfAB_we`). Its `hms` is discharged:

- the output words (`ms.we` at every `PrintC` control): every refused result
  of the call lands in the phase, `PrintG.printSvcWe`, the length below
  `2 ^ 63` by `PrintCallOk.len`;
- the byte steps (`ms.bo` at each byte): `byteOut_at`, the buffer word the
  start of a location placed at `%rdi` (`hpw`, the call site's), the bytes
  not wrapping since every placed label lies in the heap or `.data`
  (`LblRange`), which end at or below `2 ^ 32` (`hb32`, PlaceOK's
  `below32_of_placeOKAt`; `lbl_lt32`), and the count is below `2 ^ 63`.

- `printW_w2B`: `printW_w2` with `hms` from `hpw`, `hrg`, `hb32`;
- `printW_hPW`: `printCallC_of`'s `hPW` from `printW_w2B`, its `hpw` the
  hypothesis `printCallC_of` gives.
- `printW_w2B'`, `printW_hPW'`: the same at `printW_w2'`, `PrintW'`
  (`pFJ` at the call node, `PrintCallOkR` and the frames under it).
-/
import Spike.Lib.LowerX64.PrintWEW2
import Spike.Lib.X64PrintGSvc
import Spike.Lib.X64PrintByteOut
import Spike.Lib.Src.LblBelow32

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange lbl_lt32 printTop0)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (PrintC printN loadC nextC)
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

/-- **A call of `print` of a nonempty slice inside `W2`** (`printW_w2`)
under a memory side with `print`'s byte step (`hbo`) and the write abort's
justification (`hwe`): `printW_w2`'s `hms` from the buffer word the start
of a location placed at `%rdi` at every call state (`hpw`), every placed
label in the heap or `.data` (`hrg`) and the layout below `2 ^ 32`
(`hb32`). -/
theorem printW_w2B {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
    (hcall : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(fr.size : Int) - 8 - 8) R)
        (pF (-(fr.size : Int) - 8 - 8) R F) (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat)
    {ms : MemSide isa}
    (hDt : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(fr.size : Int) - 8 - 8) R F md) → ∀ s c',
      At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
        (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
      Dt s)
    (hbo : ms.bo = ByteOut p lbl) (hwe : ms.we = WeAb abi (Ab lab))
    (hpw : ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B →
      ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat)
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    PrintW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
      endPc R F ms fr Cd Bl kk pc n b o m cw Jn pw wn nv mv := by
  refine printW_w2 hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hJn he hfs hfp
    hcall hDt ?_
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

/-- **`printCallC_of`'s `hPW` inside `W2`** (`printW_w2B` at `print`'s
argument block invariant `printJ`): under memory sides with `print`'s byte
step and the write abort's justification (`hbo`, `hwe`), every placed label
in the heap or `.data` (`hrg`), the layout below `2 ^ 32` (`hb32`), the
frames below free of `ZBad` (`hfs`), and at each call (`hPer`) the caller's
continuation free of `ZBad`, the frames placed along the block,
`PrintCallOk` at the call states and the write tail at the system call.
`hPW`'s own hypothesis, the buffer word placed at `%rdi`, is `printW_w2B`'s
`hpw`. -/
theorem printW_hPW {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ms : List TermRun.Frame → MemSide isa} (hbo : ∀ fs', (ms fs').bo = ByteOut p lbl)
    (hwe : ∀ fs', (ms fs').we = WeAb abi (Ab lab))
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOk Λ ph lab rS lbl (printFrame x e c1 :: fs) (pR (-(fr.size : Int) - 8 - 8) R)
          (pF (-(fr.size : Int) - 8 - 8) R F) (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), (∀ md, F' md → pF (-(fr.size : Int) - 8 - 8) R F md) → ∀ s c',
        At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
        Dt s)) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw
  obtain ⟨he, hfp, hcall, hDt⟩ :=
    hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi
  exact printW_w2B hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl
    (fun _ _ h => h.1) he hfs hfp hcall hDt (hbo _) (hwe _) hpw hrg hb32

/-- **`printW_w2B` under frame conditions that know the call**
(`printW_w2'`, `PrintW'`): `PrintCallOkR` at the call states (`hcall`), the
suspended frames placed under every `F'` with `pFJ` (`hfr`), the write tail
under such `F'` (`hDt`). -/
theorem printW_w2B' {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra pc z g k ∧ PosOff cells lab pc)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {x : String} {e : Expr} {c1 : Ctl} {pw wn : TermRun.Word} {nv mv : Nat} {Jn : AS → Ctl → Prop}
    (hJn : ∀ σ c, Jn σ c → c = Spike.Lib.LowerNode.printTop0 pw wn mv)
    (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B)
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
  refine printW_w2' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hJn he hfs hfp
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

/-- **`printCallC_of'`'s `hPW` inside `W2`** (`printW_w2B'` at `printJ`):
`printW_hPW` with, at each call, `PrintCallOkR` at the call states and the
frames placed under every frame condition that knows the call (`pFJ`). -/
theorem printW_hPW' {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ms : List TermRun.Frame → MemSide isa} (hbo : ∀ fs', (ms fs').bo = ByteOut p lbl)
    (hwe : ∀ fs', (ms fs').we = WeAb abi (Ab lab))
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hPer : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      NoS ZBad e ∧ (∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
          (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ F' : MachineData → Prop, pFJ R F (B.nC (_root_.Executable.labels exe).label fr
          (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' →
        ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) B) ∧
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∀ (F' : MachineData → Prop), pFJ R F (B.nC (_root_.Executable.labels exe).label fr
          (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
            (printTop0 pw wn mv))) σC F' → ∀ s c',
        At exe endPc (pR (-(fr.size : Int) - 8 - 8) R) F' (pN (_root_.Executable.labels exe).label
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
          (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) (-(fr.size : Int) - 8) σC .sys) s c' →
        Dt s)) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw
  obtain ⟨he, hfp, hcall, hfr, hDt⟩ :=
    hPer c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi
  exact printW_w2B' hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl
    (fun _ _ h => h.1) he hfs hfp hcall hfr hDt (hbo _) (hwe _) hpw hrg hb32

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.printW_w2B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2B

/-- info: 'Spike.Lib.LowerX64.printW_hPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPW

/-- info: 'Spike.Lib.LowerX64.printW_w2B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_w2B'

/-- info: 'Spike.Lib.LowerX64.printW_hPW'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPW'
