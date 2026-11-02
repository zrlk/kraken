/-
**The child segment's premises at hello's root** (AArch64): `HelloWiI.hWiH_I`'s `hCP` —
`Hello.SegR.ChildPrem` at the clone's data (the worker's memory side `msWH`, the child's first memory on the
stub's region, main's `x9 .. x14`, the thread pointer `x3`, the handed stack's top) — assembled from the per-field
producers at main's `clone` (`PreRH`, the pre-spawn relation) and at the pre-spawn fragment (`HelloHPre.FrH`, the
record's placement; the route `HelloXOk.hX_ofR` takes), the one open fact left as a named premise.

Per field: `hlimT`/`hlimW` `HelloChildHlimR.hlim_cloneH` (the second TCB's words, `TcbArea` at the memory relation);
`hm` `HelloPreA.hm_clone`; `hx1` `HelloChildX1.hx1_clone`; `hwm`/`hm0`/`hwn` the packet's words; `hsvc`
`HelloAssemblyI.hsvc_preRH`; `hdm` `HelloCellOff.hdm_preRH`; `hv`/`htag`/`hvu` `HelloSpawnR.words_clone` (the
record's pointer word, `cwvH`);
`hv0`/`hv1`/`hv2` `HelloCPWords.hv012_preRH`; `hS`/`htp4`/`hSx` `HelloChildStW.childPrem_St`; `habt`
`HelloAssemblyI.habt_I`. The source-side facts hold under `VBufR`, the slot `XH`'s conjunct of the relation (`hR1`).

From the fragment: at the clone the fragment is in level 3 (`HelloHClW.pc_of_cloneH`), its placement the start's
extended twice (`I3`), so main's id label is at its TCB (`Box.hmt_H`: `x14 = pinA + 8`, `CloneInvH`'s `x14`
clause), and `x3` is the second TCB (`hx3`, the level-3 clone clause `X2H` is to carry: `x3 = tH`, from
`HelloTcbArea.x3_of_cloneMidH`; until then a premise in the clause's form, as `hClH_ofR`'s `hown2`/`hx1` were).

- `x14_ofR`, `x3_ofR`: main's `x14` and `x3` at the clone from the fragment.
- `hCP_root`: `hCP` with the `FrH Dd` antecedent. Open: `hx3` (clone side, the `X2H` clause);
  layout facts `hinit2` (the second limit word's initial value) and
  `hn3` (the pinned `.zero` reaching the second TCB's id word, `176` bytes; `131072` at the listing).
-/
import Spike.Lib.A64HelloChildHlimR
import Spike.Lib.A64HelloChildStW
import Spike.Lib.A64HelloCellOff
import Spike.Lib.HelloCPSvc
import Spike.Lib.HelloChildAbt
import Spike.Lib.A64HelloChildLim
import Spike.Lib.A64HelloChildRoot
import Spike.Lib.A64HelloBoxM
import Spike.Lib.A64HelloHClWR
import Spike.Lib.A64HelloH2Inv
import Spike.Lib.HelloHPre
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.HelloChildX1

namespace Spike.Lib.HelloRootCP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Entry Range ValRep MemRelP)
open Scc.Sem.A64 (abi pcOf textProgram)
open Scc.Sem.Kernel (callOf)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.Handover (childAfter handed)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem wordsX)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.HelloWc (tH)
open Spike.Lib.HelloPreA (ClonePreH clonePcH H0StmtH H1StmtHF cloneAtH)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.WakeW1 (mainTidW)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH cwvH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.HelloH2Inv (inv2H cloneInv2_of)
open Spike.Lib.HelloHClW (pc_of_cloneH)
open Spike.Lib.A64.PhRec (m0Of)
open Spike.Lib.HelloGOf2H (lim2AH)
open SccCode (helloProg)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => LH hp i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

section Frag

variable {μ : Marks} {Dd : ODataH} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isaLSE2}
  {Start : FragS isaLSE2} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {a : Int64} {ls0 : Lsize}

/-- **main's `x14` and `x3` at the clone from the pre-spawn fragment** (module doc): at a `clone` call the fragment
is in the third level, at the start's placement extended twice; `CloneInvH` puts main's id label at `x14`, and that
label is at main's TCB (`Box.hmt_H`); `x3` is the second TCB by the level's clone clause (`hx3`). -/
theorem x14_x3_ofR (hN : NodesA (Ly).Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl)
    (hT : TakeSiteS helloSrc μ (IH Dd)) (hCl : ∀ s, Cl s → pcOf s = clonePcH (Ly))
    (h0 : H0StmtH W0 K Dd.L0 ms0 (Ly) Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 (Ly) Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 (Ly) a (Ly).endPc Dd.L0 ls0) (hL0 : Dd.L0 = LB)
    (hx3 : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH (Ly) →
      (s.st.1.regs.getXReg .X3).toBitVec = tH (Ly).lab)
    {lbl : Lbl} {lsize : Lsize} {th : Thread isaLSE2} {s : TermRun.Cfg} {stack tls : Nat}
    (hFr : Spike.Lib.HelloHPre.FrH Dd lbl lsize th s) (hsys : abi.atSys th.st = true)
    (hcall : callOf abi th = some (.clone stack tls)) :
    (th.st.st.1.regs.getXReg .X14).toNat = ((Ly).pinA + 8#64).toNat ∧
      (th.st.st.1.regs.getXReg .X3).toBitVec = tH (Ly).lab := by
  obtain ⟨th0, hd, -, hI⟩ := hFr
  have hpc := pc_of_cloneH hN hT hCl hI hsys hcall
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ |
    ⟨l1, b1, n1, l', b', n', hl1, -, hl', -, -, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  refine ⟨?_, hx3 _ _ _ _ _ _ _ _ _ hi hpc⟩
  rw [hinv2] at hi
  obtain ⟨-, -, -, -, -, -, -, hmt, -⟩ := cloneInv2_of hi hpc
  rw [hL0] at hl1 hl' hmt
  have hme := Spike.Lib.A64.HelloPh.ChildRoot.meW_H hp i
  have hne1 : mainTidLbl 2 ≠ l1 := fun h => by rw [← h, hme] at hl1; cases hl1
  have hne' : mainTidLbl 2 ≠ l' := fun h => by
    rw [← h] at hl'
    simp only [Spike.Lib.A64ConsumerA.upd, hne1, ite_false, hme] at hl'
    cases hl'
  simp only [Spike.Lib.A64ConsumerA.upd, hne1, hne', ite_false, hme, Option.some.injEq] at hmt
  exact hmt.symm

end Frag

section Root

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {cT : ιH hp i → Loc} {cS : ιH hp i → WeakMem.Address}
  {pT : ιH hp i → Loc} {Pa : ιH hp i → Spike.Lib.Inv2Core.Inv2Params isaLSE2} {passT : State → Prop}
  {M : Spike.Lib.WakeM0.MSide (ιH hp i)} {D : WSideH (ιH hp i)} {r0 r1 : ιH hp i → Range} {asm : String} {E : Entry}
  {μ : Marks} {Dd : ODataH} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isaLSE2}
  {Start : FragS isaLSE2} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {a : Int64} {ls0 : Lsize}

/-- **`hWiH_I`'s `hCP` at the root** (module doc), with the pre-spawn fragment's antecedent. -/
theorem hCP_root (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 176 ≤ nZ)
    /- layout fact (as wake's root): the second limit word starts at `0` -/
    (hinit2 : (m0Of (Ly).Λ o.prog o.secs).initVal ⟨lim2AH (Ly), 8⟩ = 0)
    (hR1 : ∀ d s, R1 d s → R1OH arch (Ly).Λ μ Dd XH d s)
    (hDcw : ∀ w, D.cw w = w.1.cwW) (hcS : ∀ w, cS w = w.1.cS) (hr1 : ∀ w, r1 w = r1Of (Ly).lab)
    (hL0 : Dd.L0 = LB)
    (hN : NodesA (Ly).Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH (Ly))
    (h0 : H0StmtH W0 K Dd.L0 ms0 (Ly) Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 (Ly) Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 (Ly) a (Ly).endPc Dd.L0 ls0)
    /- (clone side): `x3` the second TCB at the level-3 clone states (`X2H`'s clause to be) -/
    (hx3 : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH (Ly) →
      (s.st.1.regs.getXReg .X3).toBitVec = tH (Ly).lab) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 (ιH hp i) (SRH hp i) cT cS pT Pa (GH hp i (G0H hp i)) passT M D r0 r1) (Ly).Λ asm E 0
        d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 (SRH hp i) cT cS pT Pa (GH hp i (G0H hp i)) passT M D r0 r1 (Ly).Λ w d th stack s s' s0 s1 lbl
        lsize ts j own₀ l →
      Spike.Lib.HelloHPre.FrH Dd lbl lsize th s →
      ∀ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), s1.env = [("a", T, [w0, w1, w2, w.1.cwW, w4])] →
        w4.val = mainTidW → w0.val = .loc ⟨lBH, 0⟩ 0 → w1.val = .num 2 → w2.val = .num 13 →
        ChildPrem (Ly).exe (endH hp i) (Ly).pfx (SRH hp i w).lbl (fun _ => msWH (Ly) (GH hp i (G0H hp i)) (SRH hp i) w)
          (DFrame (childR stack (-272)) (childAfter abi d.2 0 th stack tls).st.st.1)
          ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
            th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 stack) w0 w1 w2 w.1.cwW w4 13 2 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP _ hR hFr T w0 w1 w2 w4 _ h4w h0w h1w h2w
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  obtain ⟨h1R, -, -, hsys, -, -, h7, -⟩ := id hP
  have hV : HelloVBuf.VBufR s := (hR1 _ _ h1R).2.2.2.2.2
  have hth := hR.pre.threads
  obtain ⟨X, hC⟩ := hR.clone
  have hlb := HelloSpawnR.lbl_clone hR
  -- the clone call: the handed stack's top and `x3`
  obtain ⟨th', -, -, tls', cA, meW, -, -, -, -, -, -, hth', -, -, -, -, hcall, -, h3, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id hC
  obtain rfl : th = th' := by
    rw [hth] at hth'; exact List.singleton_inj.mp (congrArg Array.toList hth')
  have htop := hR.pre.top
  rw [htop] at hcall
  have etls : tls' = tls := (Scc.Sem.Kernel.Call.clone.inj (Option.some.inj (hcall.symm.trans h7))).2
  rw [etls] at h3
  -- the handed stack is the record's second take, in the pool
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13
  have hsub : (r1 w).Sub (Ly).Λ.stackPool := by rw [hr1]; exact hsub1
  obtain ⟨htop', -, hsz'⟩ := Spike.Lib.A64.HelloPh.StackB.childB_r1Of (Ly) hsub1
  rw [← hr1 w] at htop' hsz'
  have hh0 : handed d.2 0 ((r1 w).lo + (r1 w).size) = some (0, r1 w) := by simp [handed, hR.pre.held]
  have hh : handed d.2 0 stack = some (0, r1 w) := htop ▸ hh0
  -- the memory relation at the record's placement
  obtain ⟨hm, -⟩ := Spike.Lib.HelloCloneMem.memRelP_preRH hR
  -- the fragment: `x14` main's TCB, `x3` the second TCB
  obtain ⟨h14', hx3'⟩ := x14_x3_ofR hp i hN hT hCl h0 h1 hinv2 hL0 hx3 hFr hsys h7
  have htls : tls = (tH (Ly).lab).toNat := by rw [← h3]; exact congrArg BitVec.toNat hx3'
  have hpin3 := Spike.Lib.HelloTcbArea.hpin3_H hp i hz hn3
  -- the record's pointer word
  have hcw : (D.cw w).val = .loc (cS w) 0 := by rw [hDcw, hcS]; exact cwvH hp i w
  obtain ⟨hv, -, hvu⟩ := HelloSpawnR.words_clone hR hcw
  rw [hcw] at hv
  -- the cell's placed address
  obtain ⟨-, x, hx, hx13⟩ := hv
  rw [hR.hcS] at hx
  have hcA : lbl l = some x := by
    simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff, Nat.mul_zero, Nat.add_zero] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hb
  have hx13' : th.st.st.1.regs.X13.toBitVec.toNat = x := by simpa using hx13
  have e13 : th.st.st.1.regs.X13.toBitVec = BitVec.ofNat 64 x := by
    rw [← hx13']; simp
  -- `hlimT`/`hlimW`
  have hheld : d.2.held = [(0, r1Of (Ly).lab), (0, r0 w)] := by rw [← hr1 w]; exact hR.pre.held
  have htopR : (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size = stack := by rw [← hr1 w]; exact htop
  have hlim := Spike.Lib.HelloChildHlimR.hlim_cloneH hp i hpin3 hinit2 hsub1 w hm (x := d.2) (tid := 0) (th := th)
    (r0 := r0 w) hheld htopR htls
  -- `hS`/`htp4`/`hSx`
  have hmeW : BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X14).toNat = (Ly).pinA + 8#64 := by
    rw [h14', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htlsB : BitVec.ofNat 64 tls = (Ly).pinA + 112#64 := by
    rw [htls, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 112#64 = _
    rw [(Ly).lab_pin]
  obtain ⟨hS, htp4, hSx⟩ := Spike.Lib.HelloChildStW.childPrem_St hp i hm
    (Spike.Lib.A64.HelloPh.ChildRoot.hpin2_H hp i hz (by omega))
    (G := GH hp i (G0H hp i) w) (fun a ha => Spike.Lib.A64.HelloPh.ChildRoot.hG_childH' hp i w.1.cT ha)
    hmeW htlsB (x := d.2) (tid := 0) (th := th) hh0 hsub hsz' (exe := (Ly).exe) (endPc := endH hp i)
    (AbW := Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels (Ly).exe).label)
  have e14 : BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X14).toNat = th.st.st.1.regs.X14.toBitVec := by simp
  rw [e14] at hS htp4
  rw [htop] at hS hSx
  -- the slice words
  obtain ⟨hv0, hv1, hv2⟩ := HelloCPWords.hv012_preRH hV hR h0w h1w h2w
  exact {
    hlimT := hlim.1
    hlimW := fun x29 ra σ c hJ hsp => hlim.2 x29 ra σ c hJ hsp
    hm := HelloPreA.hm_clone hC hth
    hx1 := fun x29 ra σ hJ => HelloChildX1.hx1_clone hC hth _ _ _ x29 ra σ hJ
    hwm := h1w
    hm0 := by decide
    hwn := h2w
    hsvc := HelloAssemblyI.hsvc_preRH hp i ho (G0H hp i) hV hR h0w h2w
    hdm := by
      show ∀ m : MachineData, _ → Mem.loadInt m.dmem th.st.st.1.regs.X13.toBitVec 8 = none
      rw [e13, ← htop]
      exact Spike.Lib.HelloCellOff.hdm_preRH hR (Spike.Lib.HelloCloneMem.wf_LH hp i) hsub
        hh0 htop' hsz' hcA
    hv := by
      rw [hlb, cwvH hp i w, ← hcS, hR.hcS]
      exact ⟨by decide, x, by simp [Scc.Sem.wordAddr, hcA], by simpa using hx13'⟩
    htag := ⟨w.1.cS, cwvH hp i w⟩
    hvu := hlb ▸ hvu w4 h4w
    hv0 := hv0
    hv1 := hv1
    hv2 := hv2
    hS := hS
    htp4 := htp4
    hSx := hSx
    habt := HelloAssemblyI.habt_I hp i ho (G0H hp i) w }

end Root

end Spike.Lib.HelloRootCP

/-- info: 'Spike.Lib.HelloRootCP.x14_x3_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootCP.x14_x3_ofR

/-- info: 'Spike.Lib.HelloRootCP.hCP_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRootCP.hCP_root
