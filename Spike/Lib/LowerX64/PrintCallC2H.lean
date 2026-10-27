/-
**An output call held at `print`'s `ret ()`** (x86-64; the noRet walk's
option A): `printCallC_of` (`Spike/Lib/LowerX64/PrintCallC2.lean`) at
`PrintCallCH` (`Spike/Lib/LowerX64/HeldC.lean`). The machine returns to the
same continuation node; the source is not popped: an empty slice is at
`ret ()` already, a nonempty one runs at `print`'s frames to it
(`print_done_run`), and the pair is held there, its return step
(`printCall_ret`) landing at `ContC`.

- `printNRH`: `printNR` with the source's run to `print`'s `ret ()`;
- `printCallCH_of`: `printCallC_of`'s premises, at `PrintCallCH`;
- `printCallCH_of'`: `printCallC_of'`'s premises, at `PrintCallCH` (`printCallCH_of` its wrapper);
- `printCallCH_ofR`: `printCallCH_of'` with `print`'s end states asked only at
  `ret ()` (`printCallCH_of'` its wrapper);
- `printCallCH_ofRA`: `printCallCH_ofR` over `printCallC_ofA`'s premises
  (`printCallCH_ofR` its wrapper).
-/
import Spike.Lib.LowerX64.PrintCallC2
import Spike.Lib.LowerX64.HeldC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (S E Item i64 i32 xr or_)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv opdVal_upd WordsRep SRep lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Scc.Sem (ValRep)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.X64.PrintA (PrintAW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.LowerShape (printInsts)

set_option linter.unusedSimpArgs false

/-- **Where `print`'s return lands, the source held at `print`'s `ret ()`**
(`printNR` with the source's run to the return step replaced by a run at
`print`'s frames to a `ret ()`). -/
def printNRH (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (R : Region) (fp ra : BitVec 64) (c0 : Ctl) (fs fs1 : List TermRun.Frame)
    (pc' : Int64) (e : Expr) (env' : Scc.Lower.Env) (lits' : List (String × Scc.Lower.LitV))
    (cs' bufs' : List (String × Nat)) (c2 : Ctl) : ND :=
  ⟨pc', ⟨-(fr.size : Int), []⟩, fun σ c => σ.regs.get64 .rbp = R.addr 0 ∧ (∃ cR, FrameRun p (c, fs1) (cR, fs1) ∧
    cR.term = .ret .unit) ∧
    FrameRunM p (c0, fs) (c2, fs) ∧ (bodyN2 p lbl lsize i fr fp ra c2 pc' e (ofEnv2 env') lits' cs' bufs').J σ c2⟩

section Main

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`printCallCH_ofR` with the caller's slots at every state of the argument
block and the count's bound** (`PrintSlotsA`, `PrintLen`, given to `hPW`,
`hPWE` besides `PrintSlots`), so the frames along the block and
`PrintCallOkR.len` need no premise per call. -/
theorem printCallCH_ofRA {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 (printTop0 pw wn mv)) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs hG0 hT hfresh hLP _ hgrp _ hsh hxe hdg
    hrt hav hI hIt hIc hLb
  obtain ⟨rfl, rfl⟩ := hTp _ _ _ _ _ _ _ hT hxe
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8B hf; omega
  obtain ⟨B0, hPCC, -, hpc'⟩ := print_codeC hI
  obtain ⟨hc1, hcM, hc2, hc3⟩ := hPCC.cdOf hCd hBl
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, hlo1, hs1, hcap1, hk1,
    hO, hB, hL, hM, h8', hN, hC, hN', hC', hS, hKk, hz1, hz2, rfl⟩ := hPCC.toPrintCode
  let lab := (_root_.Executable.labels exe).label
  let B := pblk pc (preD lO lB lL lM l8 olo os) zs1 zM (postD lN lC lN' lC' lS lK ocap okk) zs2 zc
  have hPC : PrintCode fr pc n b o m cw B :=
    ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, hlo1, hs1, hcap1, hk1,
      hO, hB, hL, hM, h8', hN, hC, hN', hC', hS, hKk, hz1, hz2, rfl⟩
  -- the block's fresh registers are off the slice's operands and each other
  have hfw : ∀ o' ∈ [b, .reg o, m, cw], ∀ r, o' = .reg r → ∀ y k, n ≤ k → r ≠ regName y k :=
    fun o' ho r hr y k hk => atomV_fresh (hfresh.mono hk) hav y o' ho r hr
  have hb : ∀ r, b = .reg r → r ≠ regName "lo" n := fun r hr => hfw b (by simp) r hr "lo" n (by omega)
  have hm : ∀ r, m = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) := fun r hr =>
    ⟨hfw m (by simp) r hr "lo" n (by omega), hfw m (by simp) r hr "s" (n + 1) (by omega)⟩
  have hn : ∀ r, cw = .reg r → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) :=
    fun r hr => ⟨hfw cw (by simp) r hr "lo" n (by omega), hfw cw (by simp) r hr "s" (n + 1) (by omega),
      hfw cw (by simp) r hr "cap" (n + 2) (by omega)⟩
  have hsc : regName "s" (n + 1) ≠ regName "cap" (n + 2) := Scc.Lower.Inv.regName_ne (by omega)
  have hsk : regName "s" (n + 1) ≠ regName "k" (n + 3) := Scc.Lower.Inv.regName_ne (by omega)
  have fx := fun σ0 => stC_facts hf h1 lab hlo1 hs1 hcap1 hk1 hO hB hL hM h8' hN hC hN' hC' hS hKk hb hm hn hsc hsk
    (pc := pc) (zM := zM) (zc := zc) hz1 hz2 σ0
  have hsl0 := fun σ0 fl => stC_slots hf h1 lab hlo1 hs1 hcap1 hk1 hO hB hL hM h8' hN hC hN' hC' hS hKk hb hm hn hsc
    hsk (pc := pc) (zM := zM) (zc := zc) hz1 hz2 σ0 fl
  -- the frame's cells are outside `print`'s region
  have hout : ∀ k, -(fr.size : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 16 →
      R.Off k ∧ ¬ (pR (-(fr.size : Int) - 8 - 8) R).Off (k - (-(fr.size : Int) - 8 - 8)) := by
    intro k hk1 hk2 hk3
    simp only [pR, Region.Off, Region.callee]
    omega
  -- the source's names
  let t0 : Expr := .let_ x (.call "print" is a []) e
  let env' : Scc.Lower.Env := (x, .unit, []) :: env
  let lits' := (x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits
  let cs' := Scc.Lower.csAfter x cs (.call "print" is a [])
  let bufs' := Scc.Lower.bufsAfter x cs bufs (.call "print" is a [])
  have hop : Scc.Lower.opLit lcx.prog lits (.call "print" is a []) = .nil := by
    simp only [Scc.Lower.opLit, Scc.Lower.retShape, hdg, hrt, Scc.Lower.shapeOf]
  have henv' : ofEnv2 env' = (x, .unit, []) :: ofEnv2 env := ofEnv2_cons (x := x) (env := env) rfl
  -- the code's coverage
  have hok1 := (covP_printPre hf h1 hlo1 hs1 hO hB hL hM h8').ok hz1
  have hok2 := (covP_printPost hf h1 hcap1 hk1 hN hC hN' hC' hS hKk).ok hz2
  have hne1 : B.pre ≠ [] := by
    intro h; have := congrArg List.length h; simp [B, pblk, List.length_zip, hz1, preD] at this
  have hne2 : B.post ≠ [] := by
    intro h; have := congrArg List.length h; simp [B, pblk, List.length_zip, hz2, postD] at this
  -- the entries, by the call site `c1`
  let P1 : Ctl → FragS isa := fun c1 => (At exe endPc R F ⟨pc, oB fr, fun σ c =>
      printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ ∧ LocalRun p c c1 ∧
      ((bodyN2 p lbl lsize i fr fp ra c0 pc t0 (ofEnv2 env) lits cs bufs).withTp tp).J σ c⟩).at fs
  refine (SegWS.exists_pre (P := P1) fun c1 => ?_).mono_pre ?_
  rotate_left
  · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, hfs⟩
    subst fs'
    obtain ⟨⟨⟨L, sm, Bm, c1, hr, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩, htp⟩ := id hJ
    exact ⟨c1, ⟨he, hn', hdc, hpc, σ, hA, hD, ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0.trans hr, htp⟩, hr, hJ⟩,
      rfl⟩
  by_cases hex : ∃ σ, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ
  rotate_left
  · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, σ, _, _, hJ, _⟩, _⟩ => hex ⟨σ, hJ⟩
  obtain ⟨σx, hσx⟩ := hex
  obtain ⟨⟨Lx, smx, Bx, hjx, hlx, hBx, -⟩, -⟩ := hσx
  have hsh' : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf Scc.Frontend.ownSliceTy := by
    subst hprog; rw [hpd] at hdg; cases hdg; exact hsh
  obtain ⟨hgr, t', pw, wm, wn, mv, nv, hev, hwm, hwn, hm8⟩ :=
    printSite_of hjx hlx hBx.1 hgrp hav (hLP.1 a (by simp [headAtoms])) hsh'
  have hsa : Spike.Lib.Form.sevalAt (ofEnv2 env) a = some (t, [.loc b (.reg o), .one m, .one cw]) := by
    obtain ⟨pls, hpl, hs⟩ := sevalAt_ofEnv2L hgrp hav
    rw [hgr] at hpl; cases hpl; exact hs
  -- the length's and the count's operands at the call site
  have hval : ∀ σ0, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ0 →
      opdVal (rsOf fr) σ0.slot m = some mv ∧ opdVal (rsOf fr) σ0.slot cw = some nv := by
    rintro σ0 ⟨⟨_, _, _, hj0, -⟩, -⟩
    obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
    rw [hev] at hev'
    simp only [Option.some.injEq, Prod.mk.injEq] at hev'
    obtain ⟨-, rfl⟩ := hev'
    obtain ⟨-, ⟨v1, hv1, hr1⟩, ⟨v2, hv2, hr2⟩, -⟩ := hwr
    rw [hwm] at hr1
    rw [hwn] at hr2
    exact ⟨hv1.trans (congrArg some hr1.2), hv2.trans (congrArg some hr2.2)⟩
  -- the frames with `print`'s, the source after the return
  let fs1 := printFrame x e c1 :: fs
  let c2 : Ctl := ⟨e, (x, .unit, []) :: c1.env, none⟩
  let N := fun _ : Unit => printNRH p lbl lsize i fr R fp ra c0 fs fs1 pc' e env' lits' cs' bufs' c2
  let E := fun _ : Unit => printNAS lab fr lbl i x e c1
  -- the return lands at `N`
  have landR : ∀ σ0 fl, printJL p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 σ0 →
      (B.stC lab fr σ0 fl).regs.get64 .rbp = R.addr 0 → ∀ σR c',
      σR.regs.get64 .rbp = (B.stC lab fr σ0 fl).regs.rbp.toBitVec →
      (∃ cR, FrameRun p (c', fs1) (cR, fs1) ∧ cR.term = .ret .unit) →
      (∀ k, R.Off k → ¬ (pR (-(fr.size : Int) - 8 - 8) R).Off (k - (-(fr.size : Int) - 8 - 8)) →
        σR.slot k = (B.stC lab fr σ0 fl).slot k) →
      Hit (N ()) ⟨Int64.ofBitVec ((B.stC lab fr σ0 fl).slot (-(fr.size : Int) - 8)),
        ⟨-(fr.size : Int) - 8 + 8, []⟩, σR⟩ c' := by
    intro σ0 fl hJL hbp σR c' hrbp hrun hsl
    obtain ⟨⟨L, sm, Bm, hj, hl, hbB, hmB, hS⟩, hfj, hc0, -⟩ := hJL
    obtain ⟨_, _, _, _, -, -, -, -, -, hrest⟩ := fx σ0
    obtain ⟨-, -, -, hra, -⟩ := hrest fl
    -- a cell of the frame is kept from the block's entry
    have hkeep : ∀ k, -(fr.size : Int) ≤ k → k % 8 = 0 → k + 8 ≤ 16 →
        (∀ q, rsOf fr q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧ q ≠ regName "cap" (n + 2) ∧
          q ≠ regName "k" (n + 3)) → σR.slot k = σ0.slot k := by
      intro k hk1 hk2 hk3 hq
      obtain ⟨ho1, ho2⟩ := hout k hk1 hk2 hk3
      rw [hsl k ho1 ho2]
      exact hsl0 σ0 fl k (by omega) hq
    have hnone : ∀ k, 0 ≤ k → ∀ q, rsOf fr q = some k → q ≠ regName "lo" n ∧ q ≠ regName "s" (n + 1) ∧
        q ≠ regName "cap" (n + 2) ∧ q ≠ regName "k" (n + 3) := by
      intro k hk q hq; have := (rsOf_bounds hf hq).1; omega
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf fr) σR.slot o' = opdVal (rsOf fr) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hr
      refine hkeep k (by omega) hk2 (by omega) fun q' hq' => ?_
      have hqr := rsOf_inj hf hq' hr
      subst hqr
      exact ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hjE := NodeJE.unitBind hj hsl'
    refine ⟨?_, ?_, hbp ▸ hrbp, hrun, (FrameRunM.ofLocal hc0 fs).trans (FrameRunM.mem1 hj.2.1 hj.1 rfl),
      ⟨L, sm, Bm, ?_⟩, ?_, .refl _, ?_⟩
    · show pc' = Int64.ofBitVec _
      rw [hra, Int64.ofBitVec_toBitVec, hpc']; rfl
    · simp only [SO.le, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by simp [N, printNRH], rfl⟩
    · show NJB p lbl (rsOf fr) ((x, Scc.Lower.opLit lcx.prog lits (.call "print" is a [])) :: lits) cs' bufs' L sm
        lsize Bm
        e (ofEnv2 env') σR.slot c2
      rw [henv', hop]
      exact NJB.printUnit hj hl hbB hmB hS hsl'
    · exact ⟨(hkeep 0 (by omega) (by decide) (by decide) (hnone 0 (Int.le_refl 0))).trans hfj.1,
        (hkeep 8 (by omega) (by decide) (by decide) (hnone 8 (by decide))).trans hfj.2⟩
    · refine SlotRepAt.of_nodeJE hjE ?_ ?_ ?_
      · rw [← henv']; exact hIt
      · rw [← henv']; exact hLb
      · rw [← henv']; exact hIc
  -- the caller's slots at the call states
  have hcons : ∀ y, y ≠ x → lookupS (ofEnv2 env') y = lookupS (ofEnv2 env) y := by
    intro y hy
    rw [henv']
    simp [lookupS, List.find?_cons, Ne.symm hy]
  have hfv : ∀ y ∈ Scc.Sem.exprFv (Expr.let_ x (.atom .unit) e), y ∈ Scc.Sem.exprFv e ∧ y ≠ x := by
    intro y hy
    simpa [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, Scc.Sem.atVars] using hy
  have hslotsA : ∀ cE, PrintSlotsA lbl i fr n (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) x e c1 := by
    intro cE σ0 c hc sl hsl
    obtain ⟨-, hJL⟩ := hc
    obtain ⟨⟨_, _, _, hj, -⟩, -⟩ := hJL
    have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
        opdVal (rsOf fr) sl o' = opdVal (rsOf fr) σ0.slot o' := by
      intro q hq pl hpl o' ho'
      refine opdVal_upd fun r k hor hr => ?_
      exact hsl r k hr ⟨Fresh.ofEnv2 hfresh "lo" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 1)) "s" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 2)) "cap" q hq pl hpl o' ho' _ hor,
        Fresh.ofEnv2 (hfresh.mono (by omega : n ≤ n + 3)) "k" q hq pl hpl o' ho' _ hor⟩
    have hs := hj.2.2.congr hsl'
    refine SlotRepAt.of_srepE (s := (ofEnv2 env).filter (·.1 != x)) ?_ ?_ ?_ ?_
    · intro y ty' pls hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy] at hl
        exact hs y ty' pls hl
    · intro y hy
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2]
      exact hIt y hy.1
    · intro y hy ty' pls hl b' o' hb'
      have hy := hfv y hy
      rw [lookupS_filter_ne _ hy.2, ← hcons y hy.2] at hl
      exact hLb y hy.1 ty' pls hl b' o' hb'
    · intro y k v hl
      by_cases hy : y = x
      · subst hy; rw [lookupS_filter_eq] at hl; cases hl
      · rw [lookupS_filter_ne _ hy, ← hcons y hy] at hl
        exact hIc y k v hl
  have hslots : ∀ cE, PrintSlots lbl i fr Cd Bl kk lab pc n b o m cw
      (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) x e c1 := by
    intro cE B' hB' σC c hc
    obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
      hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
      hB'.toPrintCode
    obtain ⟨σ0, fl, hJ0, hσ⟩ := hc
    refine hslotsA cE σ0 c hJ0 σC.slot fun r k hr hne => ?_
    obtain ⟨-, -, hk3⟩ := rsOf_bounds hf hr
    rw [hσ]
    refine stC_slots hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM' h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn
      hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0 fl k (by omega) fun q' hq' => ?_
    have hqr := rsOf_inj hf hq' hr
    subst hqr
    exact hne
  have hlenA : ∀ cE, PrintLen fr Cd Bl kk lab pc n b o m cw
      (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) := by
    intro cE B' hB' σC c hc
    obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
      hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
      hB'.toPrintCode
    obtain ⟨σ0, fl, ⟨-, hJL⟩, rfl⟩ := hc
    obtain ⟨vb, vo, vm, vn, -, -, hvm, -, -, hrest⟩ := stC_facts hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM'
      h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0
    obtain ⟨-, -, hsi, -, -⟩ := hrest fl
    have hm' := (hval σ0 hJL).1
    rw [hvm] at hm'
    have em : vm.toNat = mv := Option.some.inj hm'
    have h8m : (vm * 8#64).toNat = mv * 8 := by
      rw [BitVec.toNat_mul, em]; simp only [BitVec.toNat_ofNat]; omega
    rw [hsi]
    split
    · omega
    · rw [h8m]; omega
  -- the frames: the call taken at the entry, the source held at `print`'s `ret ()` at the exit
  have plumb : ∀ cE : Ctl, FrameRun p (c1, fs) (cE, fs1) →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F (B.n0 fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)))
        (fun s c => Next exe endPc R F N E s c ∧ TP tp s) →
      SegWS W K p lbl ms (P1 c1) (fun s c fs' =>
        HeldC p (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs (fun _ _ _ => False) pc' e env' lits' cs' bufs')
          fs x e s c fs' ∧ c.term = .ret .unit ∨
          Ab s c fs') := by
    intro cE hrun hseg
    refine SegWS.post_run ((SegWS.pre_run (P := P1 c1) (SegWS.liftS fs1 hseg fun _ _ h => h) ?_).mono_post ?_)
    · rintro s c fs' ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJL, hr, hJ⟩, hfs⟩
      subst fs'
      exact ⟨hWL c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hI
        ⟨⟨he, hn', hdc, hpc, σ, hA, hD, hJ⟩, rfl⟩, cE, fs1,
        (FrameRun.ofLocal hr fs).trans hrun, ⟨he, hn', hdc, hpc, σ, hA, hD, rfl, hJL⟩, rfl⟩
    · rintro s c fs' ⟨⟨⟨_, he, hn', hdc, hpc, σ, hA, hD, hbp, hrun2, hgh, hJ2⟩ | ⟨_, hat⟩, htp⟩, hfs⟩ <;> subst fs'
      · obtain ⟨cR, hrR, htR⟩ := hrun2
        refine ⟨cR, fs1, hrR, .inl ⟨⟨.unit, printFrame x e c1, c2, htR, rfl, rfl, rfl, printCall_ret htR,
          .inl ⟨rfl, c2, hgh, ?_⟩⟩, htR⟩⟩
        have hat : At exe endPc R F ⟨pc', ⟨-(fr.size : Int), []⟩, fun σ' _ => σ'.regs.get64 .rbp = R.addr 0 ∧
            (bodyN2 p lbl lsize i fr fp ra c2 pc' e (ofEnv2 env') lits' cs' bufs').J σ' c2 ∧ σ'.regs.fsBase = tp⟩ s
              c2 :=
          ⟨he, hn', hdc, hpc, σ, hA, hD, hbp, hJ2, by rw [← hA.regs]; exact htp⟩
        obtain ⟨he', hn'', hdc', hpA, σ', hA', hD', -, hJ', htp'⟩ := at_rbp_addr (k := 0) hat fun _ _ h => h.1
        exact ⟨he', hn'', hdc', hpA, σ', hA', hD', hJ', htp'⟩
      · exact ⟨c, fs1, .refl _, .inr (hAb c0 x is a e c1 s c hG0 hT hat)⟩
  -- the block and the `call`, the `%fs` base kept
  have mkS1 : ∀ (cE : Ctl) (P Q : Nat → Ctl → Prop),
      PrintBlkW' (fun s c => W s c fs1) K exe endPc R F fr B
        (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)
        P Q →
      SegW (fun s c => W s c fs1) K p lbl (ms fs1)
        (At exe endPc R F (B.n0 fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE)))
        (fun s c => At exe endPc R F (B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) R) s c
          ∧
          TP tp s) := by
    rintro cE P Q ⟨hW1, hWM, hW2, hW3, _⟩
    refine (print_blocks_toC h8 (lo := -(fr.size : Int)) (hi := 16) hne1 hne2 hok1 hok2 hc1 hcM hc2 hc3 hW1 hWM hW2
      hW3 (fun σ0 _ _ => by obtain ⟨_, _, _, _, _, _, _, _, hr, _⟩ := fx σ0; exact hr) rfl
      (fun σ0 _ fl _ => by obtain ⟨_, _, _, _, _, _, _, _, _, hr⟩ := fx σ0; exact (hr fl).1) hF hR (by omega) hhi
      (by omega) (by omega)).mono_post fun s c h => ⟨h, ?_⟩
    obtain ⟨-, -, -, -, σ, hA, -, ⟨σ0, fl, ⟨-, hJL⟩, hσ⟩, -⟩ := h
    show s.st.1.regs.fsBase = tp
    rw [hA.regs, hσ, stC_fsBase]
    exact hJL.2.2.2
  by_cases hm0 : mv = 0
  · -- an empty slice: `print`'s body to `ret ()`
    obtain ⟨envR, hrunE⟩ := printCall_emptyR (fs := fs) hpd hjx.1 hev (by rw [hwm, hm0])
    let cE : Ctl := ⟨.ret .unit, envR, none⟩
    refine plumb cE hrunE ?_
    have hBW := hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI (hslotsA _) (hlenA _) (hslots _) B hPCC
    refine (mkS1 cE _ _ hBW).seq ?_
    refine print_call_emptyW_tp' (nC := B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 cE) R)
      (Pe := fun _ c => c = cE) hp hend hpin hF hR (by show R.lo ≤ -(fr.size : Int) - 8 - 8 + -40; omega)
      (by show -(fr.size : Int) - 8 - 8 + 16 ≤ R.hi; omega) (by show (-(fr.size : Int) - 8 - 8) % 8 = 0; omega) rfl
      (fun σ c ⟨⟨σ0, fl, ⟨hc, _⟩, _⟩, _⟩ => hc) ?_
      (fun σC c h F' hJF => hBW.2.2.2.2 σC c h.1 F' (PBlk.pFJ_nC hJF)) (hK fs1) ?_
    · rintro σ c ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, -⟩
      obtain ⟨vb, vo, vm, vn, -, -, hvm, -, -, hrest⟩ := fx σ0
      obtain ⟨-, -, hsi, -, -⟩ := hrest fl
      have hvm' : vm.toNat = 0 := by
        have := (hval σ0 hJL).1; rw [hvm, hm0] at this; exact Option.some.inj this
      have hv0 : vm = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hvm')
      rw [hsi, hv0]
      simp
    · rintro σC c σR c' ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, hbp⟩ hrbp hc' hsl
      subst hc'
      exact .inl ⟨(), landR σ0 fl hJL hbp σR _ hrbp ⟨_, .refl _, rfl⟩ hsl⟩
  · -- a nonempty slice: `print`'s loop
    have hen := printCall_enter (p := p) (fs := fs) hpd hd hjx.1 hev hwm hm0 hwn
    refine plumb _ hen.1 ?_
    -- the buffer word the start of a location placed at `%rdi`
    have hpwX : ∀ B', PrintCodeC fr Cd Bl kk pc n b o m cw B' → ∀ σC c, (B'.nC lab fr
        (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat := by
      intro B' hB' σC c hc
      obtain ⟨olo', os', ocap', okk', lO', lB', lL', lM', l8', lN', lC', lN'', lC'', lS', lK', zs1', zs2', zM', zc',
        hlo1', hs1', hcap1', hk1', hO', hB'', hL', hM', h8'', hN'', hC'', hN''', hC''', hS', hKk', hz1', hz2', rfl⟩ :=
        hB'.toPrintCode
      obtain ⟨σ0, fl, ⟨-, hJL⟩, rfl⟩ := hc
      obtain ⟨l, -, hpw0, -, -⟩ := print_arg_slAt hBx.1 hev hsh'
      obtain ⟨vb, vo, _vm, _vn, hvb, hvo, _, _, _, hrest⟩ := stC_facts hf h1 lab hlo1' hs1' hcap1' hk1' hO' hB'' hL' hM'
        h8'' hN'' hC'' hN''' hC''' hS' hKk' hb hm hn hsc hsk (pc := pc) (zM := zM') (zc := zc') hz1' hz2' σ0
      obtain ⟨-, hx0, -⟩ := hrest fl
      obtain ⟨⟨_, _, _, hj0, -⟩, -⟩ := hJL
      obtain ⟨_, ws, hev', -, hwr⟩ := hj0.2.2.evalAt (fun _ => rfl) hsa
      rw [hev] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq] at hev'
      obtain ⟨-, rfl⟩ := hev'
      obtain ⟨⟨vb', vo', hb', ho', hloc⟩, -⟩ := hwr
      rw [hpw0] at hloc
      obtain ⟨-, hl', hoff⟩ := hloc
      rw [hvb] at hb'
      rw [hvo] at ho'
      have e1 : vb.toNat = vb' := Option.some.inj hb'
      have e2 : vo.toNat = vo' := Option.some.inj ho'
      have ho0 : vo' = 0 := by simpa using hoff
      have hv0 : vo = 0#64 := BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
      refine ⟨l, hpw0, ?_⟩
      rw [hx0, hv0]
      simpa [BitVec.take, e1] using hl'
    obtain ⟨hBW, hsys⟩ :=
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpwX (hslotsA _) (hlenA _) (hslots _) B hPCC
    refine (mkS1 _ _ _ hBW).seq ?_
    -- the count passed to `print`
    have hcnt : ∀ σ c,
      (B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1 (printTop0 pw wn mv)) R).J
        σ c → (σ.regs.get64 .rsi).toNat = printN nv mv := by
      rintro σ c ⟨⟨σ0, fl, ⟨-, hJL⟩, hσ⟩, -⟩
      subst hσ
      obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, hrest⟩ := fx σ0
      obtain ⟨-, -, hsi, -, -⟩ := hrest fl
      obtain ⟨hm', hn'⟩ := hval σ0 hJL
      rw [hvm] at hm'
      rw [hvn] at hn'
      have em : vm.toNat = mv := Option.some.inj hm'
      have en : vn.toNat = nv := Option.some.inj hn'
      rw [hsi, printN_of_rsi (by rw [em]; exact hm8), em, en]
    refine print_call_segW_tp' (nC := B.nCR lab fr (printJ p lbl lsize fr fp ra tp c0 t0 env lits cs bufs c1
        (printTop0 pw wn mv)) R) (N := N) (E := E) (pw := fun _ => pw) (wn := fun _ => wn) (n := fun _ => nv)
      (m := fun _ => mv) hp hend hpin hF hR (by show R.lo ≤ -(fr.size : Int) - 8 - 8 + -40; omega)
      (by show -(fr.size : Int) - 8 - 8 + 16 ≤ R.hi; omega) (by show (-(fr.size : Int) - 8 - 8) % 8 = 0; omega) rfl
      (fun σ c ⟨⟨σ0, fl, ⟨hc, _⟩, _⟩, _⟩ => hc ▸ hen.2) hcnt (fun _ _ _ => hm8)
      (fun σC c h F' hJF => hBW.2.2.2.2 σC c h.1 F' (PBlk.pFJ_nC hJF)) hd (hK fs1) (hcl fs1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).2.1)
      (fun σC c h F' hJF s c' hAt => (hsys σC c h.1 (hcnt σC c h) F' (PBlk.pFJ_nC hJF) s c' hAt).2.2) ?_ ?_
    · rintro σC c σR c' ⟨⟨σ0, fl, ⟨-, hJL⟩, rfl⟩, hbp⟩ hrbp hc' hsl
      exact .inl ⟨(), landR σ0 fl hJL hbp σR c' hrbp
        (let ⟨_, hr⟩ := Spike.Lib.PrintSrc.print_done_run (p := p) hc'; ⟨_, FrameRun.ofLocalS hr _, rfl⟩)
        hsl⟩
    · rintro σC c σR c' k ⟨⟨σ0, fl, hJ0, rfl⟩, -⟩ hrdi hc' hkS
      refine .inr ⟨(), rfl, ?_, ⟨hrdi, pw, wn, nv, mv, k, hc'⟩, hslotsA _ σ0 c hJ0 σR.slot fun r j hr hne => ?_⟩
      · show SO.le ⟨-(fr.size : Int) - 56, []⟩ ⟨-(fr.size : Int) - 8 - 8 + -40, []⟩ = true
        simp only [SO.le]; simp; omega
      · -- the caller's slots kept from the call (off `print`'s region), there off the block's fresh registers
        obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hr
        obtain ⟨ho1, ho2⟩ := hout j (by omega) hk2 (by omega)
        rw [hkS j ho1 ho2]
        exact hsl0 σ0 fl j (by omega) fun q' hq' => by rw [rsOf_inj hf hq' hr]; exact hne

/-- **`printCallCH_of'` with `print`'s end states asked only at `ret ()`**
(`hPWE` at `⟨.ret .unit, envR, none⟩`, the only end the proof uses, as
`printCallC_of'`'s `hPWE`), so `printWE_hPWEJ` supplies it. -/
theorem printCallCH_ofR {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallCH_ofRA hf h1 hF hR hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw _ _ hS =>
      hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw hS)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI _ _ hS =>
      hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hI hS) hAb

/-- **`printCallCH_of` with `print`'s states asked only under frame
conditions that know the call** (`PrintW'`, `PrintWE'`, given the caller's
slots `PrintSlots`): as `printCallC_of'` is `printCallC_of` (`printCallCH_ofR`
at `print`'s `ret ()`). -/
theorem printCallCH_of' {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 cE : Ctl) (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlots lbl i fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1 cE) x e c1 →
      PrintWE' (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1 cE) cE)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallCH_ofR hf h1 hF hR hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL hPW
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' =>
      hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 ⟨.ret .unit, envR, none⟩ kk kk' pc') hAb

/-- **An output call of an `Accepted2` body held at `print`'s `ret ()`**
(`printCallC_of` at `PrintCallCH`): as `printCallC_of`, with no return
taken by the source; the return lands at `printNRH`, the pair at `print`'s
`ret ()` at `print`'s frame, its step to the continuation `ContC`. -/
theorem printCallCH_of {W : FragS isa} {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31) {lcx : Scc.Lower.Ctx}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → CdOf exe endPc pc [(i64 (.call (Scc.Emit.X64.rel g)), z)])
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    (hK : ∀ fs', (ms fs').K = some Scc.Sem.X64.abi) (hcl : ∀ fs', LocalClosed p (ms fs').bo)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    -- the source at the call
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    -- the states inside `W`
    (hWL : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits cs bufs
        s c fs → W s c fs)
    (hPW : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintW (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F (ms (printFrame x e c1 :: fs)) fr Cd Bl
        kk pc n b o m cw (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))
        pw wn nv mv)
    (hPWE : ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 cE : Ctl) (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintWE (fun s c => W s c (printFrame x e c1 :: fs)) K exe endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1 cE) cE)
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ab s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  printCallCH_of' hf h1 hF hR hlo hhi hCd hBl hp hend hpin hpd hd hprog hK hcl hTp hWL
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw _ =>
      (hPW c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hI hpw).primed)
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 cE kk kk' pc' hG0 hT hI _ =>
      (hPWE c0 pc env lits cs bufs n x is a e b o m cw c1 cE kk kk' pc' hG0 hT hI).primed) hAb

end Main

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.printCallCH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_of

/-- info: 'Spike.Lib.LowerX64.printCallCH_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_of'

/-- info: 'Spike.Lib.LowerX64.printCallCH_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_ofR

/-- info: 'Spike.Lib.LowerX64.printCallCH_ofRA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_ofRA
