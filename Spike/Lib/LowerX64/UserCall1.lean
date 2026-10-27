/-
**The user `main` of a main-only call-free `Accepted1` program as
`scc_rt_main`'s user function** (x86-64): the twins of `userCallW_of_fn`
(`Spike/Lib/LowerX64/UserCall.lean`), `userCallW_main`
(`Spike/Lib/LowerX64/AbortCall.lean`) and `userCallW_sw`
(`Spike/Lib/LowerX64/StartU.lean`), from `fn1_seg`
(`Spike/Lib/LowerX64/Fn1.lean`) at the code predicate `Cd1`
(`Spike/Lib/LowerX64/Blocks1.lean`); the twin of
`Spike/Lib/LowerA64/UserCall1.lean`.

- `InWalk1`, `walk_imms1Of`: a point of `main`'s body's walk
  (`lowerEnvs1`); at each, the lowering's environment has its immediates
  in `imms1Of [d]` (`immIn_imms1Of`).
- `userCallW1_of_fn`: the interface from the function's code facts
  (`Code1` of the open block at the entry's label, `BlocksCode` of the
  later ones, at `Cd1`) and the abort premise `hab`.
- `userCallW1_main`: with `hab_of`, the abort block's premises only when
  a block has a checked `+` (`lower1_add_insts`).
- `userCallW1_sw`: in `scc_rt_main`'s callee region after the switch.
-/
import Spike.Lib.LowerX64.Fn1
import Spike.Lib.LowerX64.BodyW1
import Spike.Lib.LowerX64.StartU
import Spike.Lib.LowerEnvImm1Of
import Spike.Lib.LowerAddChk1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW)
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB)
open Scc.Sem (Marks Range)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower1 Res1)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl K0 blkPh)
open Spike.Lib.X64.Rt (InstOk UserCallW uN0 uNx swFSL stackOff_callee)
open Spike.Lib.X64.Flow.Ret0 (StackOff CallerCells WcG LimOk limA tpOf)
open Spike.Lib.X64.StubW (abortPhOk)

/-! ## The walk -/

/-- **`t` is a point of `d`'s body's walk** (`lowerEnvs1`, a remaining
term the lowering reaches). -/
def InWalk1 (d : Decl) (t : Expr) : Prop :=
  ∃ q ∈ lowerEnvs1 [(d.arg, .unit, [])] 0 d.body, q.1 = t

/-- **At each point of a main-only `Accepted1` program's walk**, the
lowering's environment has its immediates in `imms1Of [d]`, and the point
is in the walk. -/
theorem walk_imms1Of {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) :
    ∀ q ∈ lowerEnvs1 [(d.arg, .unit, [])] 0 d.body,
      ImmIn (Scc.Lower.imms1Of [d]) (ofEnv q.2.1) q.1 ∧ InWalk1 d q.1 := by
  have hu := (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.1
  intro q hq
  refine ⟨?_, q, hq, rfl⟩
  have h := immIn_imms1Of hd (List.mem_singleton_self d)
  rw [Scc.Lower.Inv.env1_main hu] at h
  exact h q hq

/-- `main` of a main-only `Accepted1` program. -/
theorem find_main1 {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) :
    [d].find? (·.name == "main") = some d := by
  simp [List.find?, (Scc.Lower.Inv.accepted1_main hd).1]

/-! ## The interface -/

section Call

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` of a main-only call-free `Accepted1` program is
`scc_rt_main`'s user function inside `SFacts`** (`UserCallW`, post
`UPost`): `userCallW_of_fn` with the body's code at `Cd1` (`hcode`, `hbl`)
in place of `bodyIn` and its phase check, the walk `InWalk1 d` and the
immediates `imms1Of [d]`. -/
theorem userCallW1_of_fn {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res1}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hR8 : R.base.toNat % 8 = 0) (hZ8 : Z.toInt % 8 = 0)
    (hD : 8 + (fr.size : Int) ≤ D) (hD8 : D % 8 = 0)
    (hcode : Code1 fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m →
      StackOff rS (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) m)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hab : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base.toNat % 8 = 0 →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) → ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms
        (Lag [d] (· = Spike.Lib.X64Consumer.c0) (At exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (abortN (Scc.Lower.imms1Of [d]) (InWalk1 d) [d] lbl fr (_root_.Executable.labels exe).label fp ra'
            Spike.Lib.X64Consumer.c0)))
        (fun _ _ => False)) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt fr.size)
      (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 tp := by
  intro F' hR0 hF' hFF g hra hc htp
  -- the callee's region
  generalize hRc : R.callee (-8 - Z.toInt - 8 - 0) (-D) 8 = Rc at hR0 hF' hFF hFO hab ⊢
  have hlo : Rc.lo = -D := by rw [← hRc]; rfl
  have hhi : Rc.hi = 8 := by rw [← hRc]; rfl
  have hb8 : Rc.base.toNat % 8 = 0 := by
    rw [← hRc]; exact addr_toNat_mod8 R hR8 (by omega)
  have hrb8 : (rbR Rc).base.toNat % 8 = 0 := addr_toNat_mod8 Rc hb8 (by decide)
  have hrbOK : (rbR Rc).OK := rbR_ok hR0 (by omega) (by omega)
  have hFO' : ∀ m, F' m → StackOff rS Rc m := fun m h => hFO m (hFF m h).1 (hFF m h).2
  have hFOb : ∀ m, F' m → StackOff rS (rbR Rc) m :=
    fun m h => stackOff_rbR hR0 (by omega) (by omega) (hFO' m h)
  -- the source start
  have hfind := find_main1 hd
  have hu : d.argTy = .unit := (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.1
  have hQ := quiet_c1 hd
  -- the code at the return address `g.ra`
  have hcode' : Code1 fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec g.ra))
      ((_root_.Executable.labels exe).label entry) r.insts r.term := by rw [hI.labOk]; exact hra ▸ hcode
  have hbl' : BlocksCode fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec g.ra))
      (_root_.Executable.labels exe).label r.blocks := by rw [hI.labOk]; exact hra ▸ hbl
  -- the entry's `%rsp` is the region's base
  refine SegW.mono_pre (P := fun s c => At exe endPc Rc F'
      (uN0 (_root_.Executable.labels exe).label ms F fn (Int64.ofInt fr.size) g) s c ∧ Rc.base = g.sp)
    (SegW.of_imp fun hbase => ?_) fun s c hAt => ⟨hAt, ?_⟩
  rotate_left
  · obtain ⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩ := hAt
    have := hA.so .rsp 0 (by simp [SO.get, uN0])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  have hseg := fn1_seg (W := BodyW0 Λ μ own rS Tk lbl Spike.Lib.X64Consumer.c0) (K := K) (p := [d]) (lbl := lbl)
    (ms := ms) (J := (uN0 (_root_.Executable.labels exe).label ms F fn (Int64.ofInt fr.size) g).J)
    (fp := g.fp) (ra := g.ra) (c0 := Spike.Lib.X64Consumer.c0)
    hf h1 hI.lays hI.endOk hpro hr (fresh_unit d.arg) (cdOf_cd1 hI) hcode' hbl' (walk_imms1Of hd) hF' hR0
    (by omega) (by omega)
    (proW_body0 hI h1 hpro hC0 (fun _ _ h => h.1.1.trans hc ▸ .refl _) hQ
      (fun _ _ h => h.1.2.2.2.2.trans htp) hphP hR0 hb8 (by omega) (by omega) (by omega) (by omega) hmr
      (fun m h => hun m (hFF m h).1) hsub hfit hFO')
    (hWb1_of hI hf h1 hrbOK hrb8 (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) hsub hfit hFOb hC0 hQ)
    (hWs1_of hI hf h1 hrbOK hrb8 (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      (by simp only [rbR, Region.callee]; omega) hsub hfit hFOb hC0 hQ)
    (fun σ c ⟨⟨hc0, hfp, hra0, hsp, htp0⟩, hlim⟩ => by
      have hc' : c = Spike.Lib.X64Consumer.c0 := hc0.trans hc
      subst hc'
      have hlim' := hlim.mono fun m h => (hFF m h).1
      have ha : σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec = limA g.tp := by
        rw [limA, htp0]; rfl
      rw [ha]
      refine ⟨⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩, hfp, hra0, fun _ => nj_start hfind hu, .refl _⟩
      rw [hsp]; exact hlim'.room v hv)
  have hlag := (bodyW0_lag hK hseg).mono_W (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt)
    fun s c h => SFacts.dt_mono h fun _ h => h.elim
  refine (SegW.seq_left (Q := Lag [d] (· = Spike.Lib.X64Consumer.c0) (At exe endPc (rbR Rc) F'
      (abortN (Scc.Lower.imms1Of [d]) (InWalk1 d) [d] lbl fr (_root_.Executable.labels exe).label g.fp g.ra
        Spike.Lib.X64Consumer.c0)))
    ((hlag.mono_pre fun s c hAt => by
        obtain ⟨-, -, -, -, σ, -, -, hJ, -⟩ := id hAt
        exact ⟨c, hAt, .refl c, hJ.1.trans hc⟩).mono_post fun s c h => by
      obtain ⟨c', hX, hr', hcc⟩ := h
      rcases hX with ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨a, t, w, hta, hho, hev, hnm, hv, hbp⟩, hr0⟩ | hX
      · have h' : At exe endPc (rbR Rc) F' ⟨Int64.ofBitVec g.ra, ⟨16, []⟩, fun σ (_ : Ctl) =>
            σ.regs.get64 .rbp = g.fp ∧ Scc.Sem.ValRep lbl w.val (σ.regs.get64 .rax).toNat⟩ s c :=
          ⟨he, hn, hdc, hpc, σ, hA, hD', hbp, hv⟩
        obtain ⟨he, hn, hdc, hpc, σ', hA', hD'', hbp', hv'⟩ :=
          at_of_rbR (J' := fun σ (_ : Ctl) => σ.regs.get64 .rbp = g.fp ∧
            Scc.Sem.ValRep lbl w.val (σ.regs.get64 .rax).toNat) (fun _ _ h => h) h'
        have hsp := hA'.so .rsp (16 - 8) (by simp [SO.get])
        refine .inr ⟨he, hn, hdc, hpc, σ', hA', hD'', ⟨hcc, c', hcc ▸ hr0, a, t, w, hta, hho, hev, hnm, hv'⟩, hbp', ?_⟩
        rw [show σ'.regs.rsp.toBitVec = σ'.regs.get64 .rsp from rfl, hsp, Region.addr, hbase]
        rfl
      · exact .inl ⟨c', hX, hr', hcc⟩)
    (hab F' hR0 hb8 hF' hFF g.fp g.ra)).mono_post fun _ _ h => h.elim False.elim id

/-- **The user `main` of a main-only call-free `Accepted1` program is
`scc_rt_main`'s user function inside `SFacts`**, its overflow abort from
the function's `.ovf` block (`userCallW1_of_fn` with `hab_of` at the start,
the walk `InWalk1 d`): the abort block's premises only when one of the
function's blocks has a checked `+` (`lower1_add_insts`). -/
theorem userCallW1_main {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res1}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hR8 : R.base.toNat % 8 = 0) (hZ8 : Z.toInt % 8 = 0)
    (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hcode : Code1 fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m →
      StackOff rS (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) m)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Scc.Lower.imms1Of [d])
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (Abort.N lab Abort.overflow c .sys) s c' → Dt s) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt fr.size)
      (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 tp :=
  userCallW1_of_fn hd hf h1 hpro hr hI hR8 hZ8 (by omega) hD8 hcode hbl hphP hC0 hmr hun hsub hfit hFO hK
    fun F' hR0 hb0 hF' hFF _ _ =>
      hab_of hf hI
        (fun ⟨x, a, b, e, (hT : InWalk1 d _)⟩ =>
          let ⟨q, hq, hqt⟩ := hT
          hab (Spike.Lib.LowerAddChk.lower1_add_insts _ _ _ _ hr ⟨q, hq, x, a, b, e, hqt⟩))
        hprog hsysIn hphs hC0 himm hrel htk hk hKex hms hK hwr
        (rbR_ok hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide)) (addr_toNat_mod8 _ hb0 (by decide))
        (by show -D + 8 ≤ _; omega) (by show (0 : Int) ≤ 8 + 8; decide) (by show (-D + 8) % 8 = 0; omega)
        (by show (8 + 8 : Int) % 8 = 0; decide)
        (rbR_fstable hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide) hF') hsub hfit
        fun m h => stackOff_rbR hR0 (by show -D ≤ _; omega) (by show (0 : Int) ≤ 8; decide)
          (hFO m (hFF m h).1 (hFF m h).2)

/-- **The user `main` of a main-only call-free `Accepted1` program in
`scc_rt_main`'s callee region after the switch** (`userCallW_sw`'s twin):
`userCallW1_main` there (vacuous off `top`). -/
theorem userCallW1_sw {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res1}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64}
    (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (htop : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : 8 + 8 + Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hZ8 : Z.toInt % 8 = 0) (hZ : 0 ≤ Z.toInt)
    (hcode : Code1 fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode fr (Cd1 cells okPc ph lab fr (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (tpOf tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Scc.Lower.imms1Of [d])
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (Abort.N lab Abort.overflow c .sys) s c' → Dt s) :
    ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc
        ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' fn Z D (Int64.ofInt fr.size)
        (UPost [d] lbl Spike.Lib.X64Consumer.c0) ra Spike.Lib.X64Consumer.c0 (tpOf tcb) := by
  intro v F' hF'
  by_cases hv : v = top
  · subst hv
    have hR : ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8).OK :=
      Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by show _ ≤ (0 : Int); omega)
    have hb8 : ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat % 8 = 0 := addr_toNat_mod8 _ htop (by decide)
    exact userCallW1_main hd hf h1 hpro hr hI hb8 hZ8 hD hD8 hcode hbl hphP hC0 hmr (fun _ h => (hF' _ h).1.1.2)
      hsub hfit
      (fun _ h hc => stackOff_callee hR hb8 (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
        (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega) (by omega)
        (stackOff_callee hok htop (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
          (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by decide) (hF' _ h).1.2 (hF' _ h).2)
        hc)
      hab hprog hsysIn hphs himm hrel htk hk hKex hms hK hwr
  · intro F'' _ _ hFF _ _ _ _
    exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, hD', _⟩ => hv (hF' _ (hFF _ hD').1).1.1.1

end Call

end Spike.Lib.LowerX64
