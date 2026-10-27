/-
**The user `main` of a main-only call-free `Accepted1` program as
`scc_rt_main`'s user function** (AArch64): the twins of
`userCallW_of_fn` (`Spike/Lib/LowerA64/UserCall.lean`), `userCallW_main`
(`Spike/Lib/LowerA64/AbortCall.lean`) and `userCallW_sw`
(`Spike/Lib/LowerA64/StartU.lean`), from `fn1_seg`
(`Spike/Lib/LowerA64/Fn1.lean`) at the code predicate `Cd1`
(`Spike/Lib/LowerA64/Blocks1.lean`).

- `InWalk1`, `walk_imms1Of`: a point of `main`'s body's walk
  (`lowerEnvs1`); at each, the lowering's environment has its immediates
  in `imms1Of [d]` (`immIn_imms1Of`).
- `userCallW1_of_fn`: the interface from the function's code facts
  (`Code1` of the open block at the entry's label, `BlocksCode` of the
  later ones, at `Cd1`) and the abort premise `hab`.
- `userCallW1_main`: with `hab_of`, the abort block's premises only when
  a block has a checked `+` (`lower1_add_insts`).
- `userCallW1_sw`: in the new stack's region after the switch.
-/
import Spike.Lib.LowerA64.Fn1
import Spike.Lib.LowerA64.BodyW1
import Spike.Lib.LowerA64.StartU
import Spike.Lib.LowerEnvImm1Of
import Spike.Lib.LowerAddChk1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.Form (NodeJ SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower1 Res1)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl blkPh K0)
open Spike.Lib.A64.Rt (InstOk UserCallW uN0 uNx swFSL)
open Spike.Lib.A64.Flow.Ret0 (StackOff WcG LimOk limA tcbA_limA)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.A64.StubW (abortPhOk)

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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` of a main-only call-free `Accepted1` program is
`scc_rt_main`'s user function inside `SFacts`** (`UserCallW`, post
`UPost`): `userCallW_of_fn` with the body's code at `Cd1` (`hcode`, `hbl`)
in place of `bodyIn` and its phase check, the walk `InWalk1 d` and the
immediates `imms1Of [d]`. -/
theorem userCallW1_of_fn {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {cx : FnCtx} {r : Res1}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hcode : Code1 cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m →
      StackOff rS (R.callee (-Z.toInt) (-D) 0) m)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hab : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) → ∀ fp ra' : BitVec 64,
      SegW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms
        (Lag [d] (· = Spike.Lib.A64Consumer.c0) (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (abortN (Scc.Lower.imms1Of [d]) (InWalk1 d) [d] lbl cx (_root_.Executable.labels exe).label fp ra'
            Spike.Lib.A64Consumer.c0)))
        (fun _ _ => False)) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 tp := by
  intro F' hR0 hal0 hF' hFF g hra hc htp
  have hge := frame_ge16 hf
  have hfind := find_main1 hd
  have hu : d.argTy = .unit := (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.1
  have hQ := quiet_c1 hd
  have hlo0 : (R.callee (-Z.toInt) (-D) 0).lo ≤ -(cx.frame : Int) := by show -D ≤ _; omega
  have hhi0 : 0 ≤ (R.callee (-Z.toInt) (-D) 0).hi := Int.le_refl 0
  have hl0 : (R.callee (-Z.toInt) (-D) 0).lo % 8 = 0 := by show (-D) % 8 = 0; omega
  have hh0 : (R.callee (-Z.toInt) (-D) 0).hi % 8 = 0 := rfl
  have hFO' : ∀ m, F' m → StackOff rS (R.callee (-Z.toInt) (-D) 0) m :=
    fun m h => hFO m (hFF m h).1 (hFF m h).2
  subst hra
  have hcode' : Code1 cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec g.ra))
      ((_root_.Executable.labels exe).label entry) r.insts r.term := by rw [hI.labOk]; exact hcode
  have hbl' : BlocksCode cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec g.ra))
      (_root_.Executable.labels exe).label r.blocks := by rw [hI.labOk]; exact hbl
  have hseg := fn1_seg (W := BodyW0 Λ μ own rS Tk lbl Spike.Lib.A64Consumer.c0) (K := K) (p := [d]) (lbl := lbl)
    (ms := ms) (J := (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn (Int64.ofInt cx.frame) g).J)
    (fp := g.fp) (ra := g.ra) (c0 := Spike.Lib.A64Consumer.c0)
    hf h1 h16 hI.lays hI.endOk hpro hr (fresh_unit d.arg) (cdOf_cd1 hI) hcode' hbl' (walk_imms1Of hd)
    hF' hR0 hal0 hlo0 hhi0
    (proW_body0 hI hf h1 h16 hpro hC0 (fun _ _ h => h.1.1.trans hc ▸ .refl _) hQ
      (fun _ _ h => h.1.2.2.2.2.trans htp) hphP hR0 hal0 hlo0 hhi0 hl0 hh0 hmr
      (fun m h => hun m (hFF m h).1) hsub hfit hFO')
    (hWb1_of hI hf h1 h16 hR0 hal0 hlo0 hhi0 hl0 hh0 hsub hfit hFO' hC0 hQ)
    (hWs1_of hI hf h1 h16 hR0 hal0 hlo0 hhi0 hl0 hh0 hsub hfit hFO' hC0 hQ)
    (fun σ c ⟨⟨hc0, h29, h30, hsp, htp0⟩, hlim⟩ => by
      have hc' : c = Spike.Lib.A64Consumer.c0 := hc0.trans hc
      subst hc'
      have hlim' := hlim.mono fun m h => (hFF m h).1
      refine ⟨?_, h29, h30, fun _ => nj_start hfind hu, .refl _⟩
      rw [show tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit) = limA g.tp from tcbA_limA htp0]
      refine ⟨hlim'.rt, hlim'.mp, hlim'.unmapped, fun v hv => ?_⟩
      rw [hsp]; exact hlim'.room v hv)
  have hlag := (bodyW0_lag hK hseg).mono_W (W' := fun s c => SFacts Λ μ own rS Tk lbl s c Dt)
    fun s c h => SFacts.dt_mono h fun _ h => h.elim
  refine (SegW.seq_left (Q := Lag [d] (· = Spike.Lib.A64Consumer.c0) (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
      (abortN (Scc.Lower.imms1Of [d]) (InWalk1 d) [d] lbl cx (_root_.Executable.labels exe).label g.fp g.ra
        Spike.Lib.A64Consumer.c0)))
    ((hlag.mono_pre fun s c hAt => by
        obtain ⟨-, -, -, -, σ, -, -, hJ, -⟩ := id hAt
        exact ⟨c, hAt, .refl c, hJ.1.trans hc⟩).mono_post fun s c h => by
      obtain ⟨c', hX, hr', hcc⟩ := h
      rcases hX with ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨a, t, w, hta, hho, hev, hnm, hv, h29, h30⟩, hr0⟩ | hX
      · exact .inr ⟨he, hn, hdc, hpc, σ, hA, hD', ⟨hcc, c', hr0, a, t, w, hta, hho, hev, hnm, hv⟩, h29, h30⟩
      · exact .inl ⟨c', hX, hr', hcc⟩)
    (hab F' hR0 hal0 hF' hFF g.fp g.ra)).mono_post fun _ _ h => h.elim False.elim id

/-- **The user `main` of a main-only call-free `Accepted1` program is
`scc_rt_main`'s user function inside `SFacts`**, its overflow abort from
the function's abort block (`userCallW1_of_fn` with `hab_of` at the start,
the walk `InWalk1 d`): the abort block's premises only when one of the
function's blocks has a checked `+` (`lower1_add_insts`). -/
theorem userCallW1_main {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {cx : FnCtx} {r : Res1}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop} {Z : Int64} {D : Int}
    {tp : UInt64} {ra : BitVec 64} (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hcode : Code1 cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m →
      StackOff rS (R.callee (-Z.toInt) (-D) 0) m)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Scc.Lower.imms1Of [d])
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s) :
    UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc R F fn Z D
      (Int64.ofInt cx.frame) (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 tp :=
  userCallW1_of_fn hd hf h1 h16 hpro hr hI hD hD8 hcode hbl hphP hC0 hmr hun hsub hfit hFO hK
    fun F' hR0 hal0 hF' hFF _ _ =>
      hab_of hf h16 hI
        (fun ⟨x, a, b, e, (hT : InWalk1 d _)⟩ =>
          let ⟨q, hq, hqt⟩ := hT
          hab (Spike.Lib.LowerAddChk.lower1_add_insts _ _ _ _ hr ⟨q, hq, x, a, b, e, hqt⟩))
        hprog hphs hC0 himm hrel htk hk hKex hms hK hwr hR0 hal0
        (by show -D ≤ _; omega) (Int.le_refl 0) (by show (-D) % 8 = 0; omega) rfl hF' hsub hfit
        fun m h => hFO m (hFF m h).1 (hFF m h).2

/-- **The user `main` of a main-only call-free `Accepted1` program in the
new stack's region** (`userCallW_sw`'s twin): `userCallW1_main` in
`swR v (-L) 0` under `swFSL`. -/
theorem userCallW1_sw {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {cx : FnCtx} {r : Res1}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64}
    (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (htop : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL : Z.toInt + D ≤ L) (hL8 : L % 8 = 0)
    (hZ8 : Z.toInt % 8 = 0) (hZ : 0 < Z.toInt)
    (hcode : Code1 cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) (lab entry) r.insts r.term)
    (hbl : BlocksCode cx (Cd1 prog okPc ph lab cx (Int64.ofBitVec ra)) lab r.blocks)
    (hphP : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (UInt64.ofBitVec tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Scc.Lower.imms1Of [d])
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s) :
    ∀ v, UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 (UInt64.ofBitVec tcb) := fun v =>
  userCallW1_main hd hf h1 h16 hpro hr hI hD hD8 hcode hbl hphP hC0 hmr (fun _ h => h.1.2) hsub hfit
    (fun m h hcc => by
      obtain ⟨⟨rfl, -⟩, hso⟩ := h
      have hR8 : (swR v (-L) 0).base.toNat % 8 = 0 := by show v.toNat % 8 = 0; omega
      exact stackOff_callee hok hR8 (by show (-L) % 8 = 0; omega) rfl (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by omega) hso hcc)
    hab hprog hphs himm hrel htk hk hKex hms hK hwr

end Call

end Spike.Lib.LowerA64
