/-
**An output call at a lowering's immediates other than the world's**
(x86-64): `printCallC_instA`, `printCallCH_instA`
(`Spike/Lib/LowerX64/PrintCallInstA.lean`) with the segment's table `i`
apart from the world's `Λ.imms`, as when the code facts are at the
lowering's `imms2Of p` and `W2` at the theorem's `imms2Me Λ p`: every entry of
`i` is `Λ.imms`'s (`hiL`, the node at the `let` placed at `Λ.imms` too) and
the two agree at each `print` call's continuation (`hie`). The return
address's phase and write-abort facts come from the calls at `BlC2`
(`hBl2`: `printRa_ph`, `printRa_notAb`).

- `bodyN2_imms`, `letAt_imms`: the node at a `let` at a table whose entries
  `i`'s are;
- `printCallC_instAI`, `printCallCH_instAI`: `PrintCallC`, `PrintCallCH` at
  `i` (`printCallC_ofA`, `printCallCH_ofRA` at `i`, their `hWL` from
  `printWL_w2` by `letAt_imms`, their `hPW`, `hPWE` from `printW_hPWA`,
  `printWE_hPWEA` at `hie`).
-/
import Spike.Lib.LowerX64.PrintCallInstA
import Spike.Lib.LowerX64.PrintCallOkF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Lower.InvX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable Abs DFrame arun)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.LowerShape (printInsts)
open Scc.Lower.Inv (regName)
open Spike.Lib.PrintSrc (printLD)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The node at a body's point at a table whose entries `i`'s are**: only
the control's placement reads the table (`SlotRepAt`'s `ImmIn`). -/
theorem bodyN2_imms {i i' : Expr → String → Nat → Option Nat}
    (hii : ∀ t x k v, i t x k = some v → i' t x k = some v) {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}
    {c0 : Ctl} {pc : Int64} {t : Expr} {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} {σ : AS} {c : Ctl}
    (h : (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).J σ c) :
    (bodyN2 p lbl lsize i' fr fp ra c0 pc t s lits cs bufs).J σ c := by
  obtain ⟨hN, hF, hL, s', hS, htot, hb, hI⟩ := h
  exact ⟨hN, hF, hL, s', hS, htot, hb, fun x k v hv => hii _ _ _ _ (hI x k v hv)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The node at a `let` at a table whose entries `i`'s are**
(`bodyN2_imms`). -/
theorem letAt_imms {i i' : Expr → String → Nat → Option Nat}
    (hii : ∀ t x k v, i t x k = some v → i' t x k = some v) {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}
    {tp : UInt64} {c0 : Ctl} {pc : Int64} {t : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame}
    (h : LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc t env lits cs bufs s c fs') :
    LetAt p lbl lsize i' fr exe endPc R F fp ra tp c0 fs pc t env lits cs bufs s c fs' := by
  obtain ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ, htp⟩, hfs⟩ := h
  exact ⟨⟨he, hn, hdc, hpc, σ, hA, hD, bodyN2_imms hii hJ, htp⟩, hfs⟩

/-- **The return address in `done`'s phase at a call of `print`'s
argument block** whose `call` is at `BlC2` (`printRa_ph`, `BlC`'s phase of
the fall-through). -/
theorem hraP_of_blC2 {kp : Nat} (hp : Scc.Cert.Rt.X64.Lays exe cells kp)
    (hlab : (_root_.Executable.labels exe).label = lab)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} {ra0 pc : Int64} {z k : Nat}
    (h : Spike.Lib.LowerX64.BlC2 cells okPc ph lab fr ra0 pc z Scc.Lower.Names.print k) :
    ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat := by
  obtain ⟨-, -, -, -, -, -, -, hph'⟩ := h.1
  rw [← hph']
  exact printRa_ph hp hlab hpr hph h

/-- **An output call at `PrintCallC` at the lowering's immediates `i`**
(`printCallC_ofA` at `i`): `printCallC_instA`'s premises with the return
address's facts from the calls at `BlC2` (`hBl2`; per call, `hraP_of_blC2`
at the argument block's `call`, `printRa_notAb`), the node at the `let`
placed at `Λ.imms` (`hiL`, `letAt_imms`), the caller's slots at the
continuation the same at both (`hie`). -/
theorem printCallC_instAI {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
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
    {i : Expr → String → Nat → Option Nat} (hiL : ∀ t x k v, i t x k = some v → Λ.imms t x k = some v)
    (hie : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → Λ.imms e = i e)
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hBl2 : ∀ pc z k, Bl pc z Scc.Lower.Names.print k →
      Spike.Lib.LowerX64.BlC2 cells okPc ph lab fr ra0 pc z Scc.Lower.Names.print k)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 i T Ax := by
  have hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab :=
    fun _ _ _ h => printRa_notAb hI.lays hI.labOk hpr habI (hBl2 _ _ _ h)
  intro c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 hi
  obtain ⟨B, hB, -, -⟩ := print_codeC hi
  have hraP := hraP_of_blC2 hI.lays hI.labOk hpr hph (hBl2 _ _ _ hB.bl)
  exact printCallC_ofA (i := i) hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (fun c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hi' hL =>
      printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
        (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
        (fun _ _ h => h) hG0F fp ra tp c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hi'
        (letAt_imms hiL hL))
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi' hpw hSA hlen hS => by
      have he := hie x is a e hT
      exact printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs
        hFP fp ra tp hNoS hraP hraAb hDtP c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT
        hi' hpw (by simpa only [PrintSlotsA, he] using hSA) hlen (by simpa only [PrintSlots, he] using hS))
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi' hSA hlen hS => by
      have he := hie x is a e hT
      exact printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra
        tp hNoS hraP hraAb c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi'
        (by simpa only [PrintSlotsA, he] using hSA) hlen (by simpa only [PrintSlots, he] using hS))
    hAb c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 hi

/-- **An output call at `PrintCallCH` at the lowering's immediates `i`**
(`printCallCH_ofRA` at `i`): `printCallCH_instA`'s premises with the return
address's facts from the calls at `BlC2` (`hBl2`; per call, `hraP_of_blC2`
at the argument block's `call`, `printRa_notAb`), the node at the `let`
placed at `Λ.imms` (`hiL`, `letAt_imms`), the caller's slots at the
continuation the same at both (`hie`). -/
theorem printCallCH_instAI {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
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
    {i : Expr → String → Nat → Option Nat} (hiL : ∀ t x k v, i t x k = some v → Λ.imms t x k = some v)
    (hie : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → Λ.imms e = i e)
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hBl2 : ∀ pc z k, Bl pc z Scc.Lower.Names.print k →
      Spike.Lib.LowerX64.BlC2 cells okPc ph lab fr ra0 pc z Scc.Lower.Names.print k)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl i x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 i T Ax := by
  have hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab :=
    fun _ _ _ h => printRa_notAb hI.lays hI.labOk hpr habI (hBl2 _ _ _ h)
  intro c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 hi
  obtain ⟨B, hB, -, -⟩ := print_codeC hi
  have hraP := hraP_of_blC2 hI.lays hI.labOk hpr hph (hBl2 _ _ _ hB.bl)
  exact printCallCH_ofRA (i := i) hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (fun c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hi' hL =>
      printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
        (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
        (fun _ _ h => h) hG0F fp ra tp c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 hT hi'
        (letAt_imms hiL hL))
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi' hpw hSA hlen hS => by
      have he := hie x is a e hT
      exact printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs
        hFP fp ra tp hNoS hraP hraAb hDtP c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT
        hi' hpw (by simpa only [PrintSlotsA, he] using hSA) hlen (by simpa only [PrintSlots, he] using hS))
    (fun c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi' hSA hlen hS => by
      have he := hie x is a e hT
      exact printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra
        tp hNoS hraP hraAb c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi'
        (by simpa only [PrintSlotsA, he] using hSA) hlen (by simpa only [PrintSlots, he] using hS))
    hAb c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 hi

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.bodyN2_imms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.bodyN2_imms

/-- info: 'Spike.Lib.LowerX64.letAt_imms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.letAt_imms

/-- info: 'Spike.Lib.LowerX64.hraP_of_blC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hraP_of_blC2

/-- info: 'Spike.Lib.LowerX64.printCallC_instAI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_instAI

/-- info: 'Spike.Lib.LowerX64.printCallCH_instAI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_instAI
