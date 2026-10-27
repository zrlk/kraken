/-
**The start's switch and the user `main` with an extra frame `Fw`**
(AArch64): `swUW_gen_dt` (`Spike/Lib/LowerA64/StartU.lean`) and
`userCallW1_sw` (`Spike/Lib/LowerA64/UserCall1.lean`), `userCallW_sw` at the frame
`Fw ∧ swFSL …` after the switch (`SwUWF`, `Spike/Lib/Rt/A64SegsF.lean`).

- `swUWF_gen_dt`: the switch's and `scc_rt_main`'s states inside `SFacts … Dt`;
- `userCallW1_swF`, `userCallW_swF`: the user `main`'s interface (`Accepted1`,
  `Accepted0`) for every value of the new `sp`.
-/
import Spike.Lib.LowerA64.UserCall1
import Spike.Lib.Rt.A64SegsF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Sem (Marks Range ValRep)
open Spike.Lib.Form (lookupS SEnv)
open Spike.Lib.LowerNode (AbSrc)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl Lsize blkPh msOf Placed K0)
open Spike.Lib.A64.Rt (InstOk UserCallW MainCode MainUW SwUWF swFSL)
open Spike.Lib.A64.Flow.Ret0 (StackOff StackM CallerCells limA swF)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.A64.StubW (abortPhOk)
open Scc.Lower.Inv (lower1 Res1)
open Scc.Cert.Rt.A64 (Lays endOf)

section DtF

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

private theorem dtJ {Dt : State → Prop} {J : AS → Ctl → Prop} :
    ∀ σ c, J σ c → ∃ c', J σ c' ∧ ∀ s, SFacts Λ μ own rS Tk lbl s c' → SFacts Λ μ own rS Tk lbl s c Dt :=
  fun _ c h => ⟨c, h, fun _ hs => hs.dt_mono fun _ h => h.elim⟩

set_option maxHeartbeats 800000 in
open Spike.Lib.A64.Rt.MainU in
/-- **`swUW_gen_dt` with the extra frame `Fw` after the switch**: the switch's and `scc_rt_main`'s
states inside `SFacts … Dt`, the user function's interface there (`hU`);
the premises otherwise `swUW_gen`'s. -/
theorem swUWF_gen_dt {p : Prog} {lbl' : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {Dt : State → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hin : Spike.Lib.A64.Flow.Ret0.startTailIn prog = true)
    {mc : MainCode} (hmain : Spike.Lib.A64.Rt.mainUIn prog mc = true) {Post : Ctl → BitVec 64 → Prop} {c0 : Ctl}
    (hC0 : CFacts Λ lbl c0) (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc)
    (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {Fw : _root_.Mem 64 → Prop} {tcb top : BitVec 64} {L : Int} {D : Int} {ZU : Int64}
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL : mc.Z.toInt ≤ L) (hL8 : L % 8 = 0)
    (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (UInt64.ofBitVec tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v, UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' ms exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)) :
    SwUWF (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' exe endPc R (fun m => F m ∧ StackM rS m) Fw ms rS
      tcb top c0 L mc D ZU Post := by
  have h := hin
  simp only [Spike.Lib.A64.Flow.Ret0.startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨-, bSw⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_, hU⟩
  · refine NodeW.mapC rfl rfl ?_ dtJ
    rw [hI.labOk]
    exact Spike.Lib.A64.Rt.nodeW_flowReg_post hI (by simp [Spike.Lib.A64.Flow.RegOnly]) bSw rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1 hsw.sw.2 hsub
  · by_cases hv : v = top
    · subst hv
      refine BlkW.mapC rfl rfl ?_ dtJ
      rw [hI.labOk]
      exact Spike.Lib.A64.Rt.blkW_postO hI bMain rfl (Spike.Lib.A64.Rt.startMain_okL (-L) 0) hok h16
        (Int.le_refl _) (Int.le_refl _) (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main
        (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false startMain_noRet k hk r hr).elim)
        (fun _ _ _ => rfl) (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hsub hfit
        (fun _ h => h.2.2)
    · exact Spike.Lib.A64.Rt.blkW_ofFalse fun _ h => hv h.2.1.1
  · by_cases hv : v = top
    · subst hv
      exact MainUW.dt (Spike.Lib.A64.Rt.mainUW_gen hI hmain hC0 hPost hph hok h16 (by show -L ≤ _; omega)
        (Int.le_refl _) (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hZ16 hZ hk hmr
        (fun _ h => h.2.1.2) hsub hfit (fun _ h => h.2.2))
    · exact Spike.Lib.A64.Rt.mainUW_ofFalse fun _ h => hv h.2.1.1

end DtF

section CallF

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **`userCallW1_sw` with the extra frame `Fw`**: the user `main` of a
main-only call-free `Accepted1` program in the new stack's region: `userCallW1_main` in
`swR v (-L) 0` under `Fw ∧ swFSL`. -/
theorem userCallW1_swF {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) {cx : FnCtx} {r : Res1}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64} {Fw : _root_.Mem 64 → Prop}
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
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 (UInt64.ofBitVec tcb) := fun v =>
  userCallW1_main hd hf h1 h16 hpro hr hI hD hD8 hcode hbl hphP hC0 hmr (fun _ h => h.2.1.2) hsub hfit
    (fun m h hcc => by
      obtain ⟨-, ⟨rfl, -⟩, hso⟩ := h
      have hR8 : (swR v (-L) 0).base.toNat % 8 = 0 := by show v.toNat % 8 = 0; omega
      exact stackOff_callee hok hR8 (by show (-L) % 8 = 0; omega) rfl (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by omega) hso hcc)
    hab hprog hphs himm hrel htk hk hKex hms hK hwr

/-- **`userCallW_sw` with the extra frame `Fw`**: the user `main` of an
`Accepted0` program in the new stack's region `swR v (-L) 0` under
`Fw ∧ swFSL`, for every value `v` of the new `sp`. -/
theorem userCallW_swF {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx} {r : Scc.Lower.Inv.Res}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : Scc.Lower.Inv.lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn prog cx entry 0 r.insts r.ret = true)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64} {Fw : _root_.Mem 64 → Prop}
    (hD : (cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (htop : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL : Z.toInt + D ≤ L) (hL8 : L % 8 = 0)
    (hZ8 : Z.toInt % 8 = 0) (hZ : 0 < Z.toInt)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cx entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts Λ lbl Spike.Lib.A64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (UInt64.ofBitVec tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hab : r.insts ≠ [] → blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Spike.Lib.LowerNode.immsOf d)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s) :
    ∀ v, UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K [d] lbl ms exe endPc (swR v (-L) 0)
      (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 (UInt64.ofBitVec tcb) := fun v =>
  userCallW_main hd hf h1 h16 hpro hr hbody hI hD hD8 hphB hphP hC0 hmr (fun _ h => h.2.1.2) hsub hfit
    (fun m h hcc => by
      obtain ⟨-, ⟨rfl, -⟩, hso⟩ := h
      have hR8 : (swR v (-L) 0).base.toNat % 8 = 0 := by show v.toNat % 8 = 0; omega
      exact stackOff_callee hok hR8 (by show (-L) % 8 = 0; omega) rfl (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by omega) hso hcc)
    hab hprog hphs himm hrel htk hk hKex hms hK hwr

end CallF

end Spike.Lib.LowerA64
