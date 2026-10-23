/-
**The start's switch and `scc_rt_main` with the user `main`, inside the
consumer's facts with the overflow stub's write tail** (AArch64): the pieces
of `startU_segW` (`Spike/Lib/Rt/A64Segs.lean`) that the user `main` feeds,
at `W := SFacts … Dt` (the write tail `Dt` live: the overflow stub writes
inside the user's callee region).

- `uPost_exit`: `startU_segW`'s `hexit` at the post `UPost` under the
  placement's memory side (`msOf`): a control at `main`'s `ret` of the
  number in `x0` is `main`'s exit with that number mod 256 (`MainExit`).
- `MainUW.dt`: `scc_rt_main`'s own obligations at `Dt = False` hold at any
  `Dt` (`SFacts.dt_mono`).
- `swUW_gen_dt`: `swUW_gen` (`Spike/Lib/Rt/A64RtMainU.lean`) with the user
  function's interface and the conclusion at `SFacts … Dt`.
- `userCallW_sw`: the user `main`'s interface (`userCallW_main`,
  `Spike/Lib/LowerA64/AbortCall.lean`) in the new stack's region after the
  switch (`swR`, `swFSL`), for every value of the new `sp`.
-/
import Spike.Lib.LowerA64.AbortCall
import Spike.Lib.Rt.A64RtMainU

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
open Spike.Lib.A64.Rt (InstOk UserCallW MainCode MainUW SwUW swFSL)
open Spike.Lib.A64.Flow.Ret0 (StackOff StackM CallerCells limA swF)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.A64.StubW (abortPhOk)

/-! ## `main`'s exit -/

/-- **`main`'s exit at the post `UPost`** (`startU_segW`'s `hexit`), under
the placement's memory side: from the start `c0` a local run reaches
`ret a` of a number represented by `x0` (`RetV`), placed in `x0`, whose
return is the exit with the number mod 256. -/
theorem uPost_exit {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Own} {lbl : Lbl} {ls0 : Lsize} {ms : MemSide isaLSE2} (hms : ms = msOf Λ μ rd G own lbl ls0)
    {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (v : BitVec 64), UPost p lbl c0 c v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExit p ms s c v.toNat := by
  subst hms
  rintro R' F' s c v ⟨rfl, c', hr, a, t, w, hta, -, hev, ⟨n, hn⟩, hv⟩ ⟨-, -, -, -, σ, hA, -, hx⟩ -
  have hx0 : Scc.Sem.A64.regVal s (.x 0) = v := by
    show s.st.1.regs.X0.toBitVec = v
    rw [hA.regs]; exact hx
  refine ⟨c', hr, ?_, ?_⟩
  · show Placed Λ lbl s c'
    cases a with
    | var y =>
      refine ⟨fun x k => if x = y ∧ k = 0 then some (.one (.reg (.x 0))) else none, ?_, ?_, ?_⟩
      · intro x ty ws hl k wd wp hk hp
        dsimp only at hp
        split at hp
        · obtain ⟨rfl, rfl⟩ := ‹x = y ∧ k = 0›
          cases hp
          have hw : (ty, ws) = (t, [w]) := Option.some.inj (hl.symm.trans hev)
          cases hw
          cases hk
          exact ⟨v.toNat, congrArg (fun b : BitVec 64 => some b.toNat) hx0, hv⟩
        · cases hp
      · intro x hx ty ws hl k hk
        rw [hta] at hx
        simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
        subst hx
        have hw : (ty, ws) = (t, [w]) := Option.some.inj (hl.symm.trans hev)
        cases hw
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨.one (.reg (.x 0)), by simp⟩
      · intro x k m h
        dsimp only at h
        split at h <;> cases h
    | lit m =>
      refine ⟨fun _ _ => none, ?_, ?_, ?_⟩
      · intro _ _ _ _ _ _ _ _ hp; cases hp
      · intro x hx
        rw [hta] at hx
        simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
      · intro _ _ _ h; cases h
    | unit => cases hev
  · intro s0 th h0 ht he hs
    unfold Scc.Sem.SrcSem.mainExit
    rw [h0]
    simp only [ht, hta, hs, he, hev, hn]
    rw [hn] at hv
    rw [hv.2]
    rfl

/-! ## The obligations at a live write tail -/

section Dt

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

private theorem dtJ {Dt : State → Prop} {J : AS → Ctl → Prop} :
    ∀ σ c, J σ c → ∃ c', J σ c' ∧ ∀ s, SFacts Λ μ own rS Tk lbl s c' → SFacts Λ μ own rS Tk lbl s c Dt :=
  fun _ c h => ⟨c, h, fun _ hs => hs.dt_mono fun _ h => h.elim⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_main`'s own obligations at any write tail.** -/
theorem MainUW.dt {Dt : State → Prop} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2}
    {mc : MainCode} {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.A64.Flow.Ret0.MainG}
    (h : MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms mc Post g) :
    MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F ms mc Post g :=
  ⟨ProW.mapC h.pro dtJ, BlkW.mapC rfl rfl h.call dtJ,
    ⟨BlkW.mapC rfl rfl h.exit.w0 dtJ, NodeW.mapC rfl rfl h.exit.w1 dtJ⟩⟩

set_option maxHeartbeats 800000 in
open Spike.Lib.A64.Rt.MainU in
/-- **`swUW_gen` at a live write tail**: the switch's and `scc_rt_main`'s
states inside `SFacts … Dt`, the user function's interface there (`hU`);
the premises otherwise `swUW_gen`'s. -/
theorem swUW_gen_dt {p : Prog} {lbl' : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {Dt : State → Prop}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) (hin : Spike.Lib.A64.Flow.Ret0.startTailIn prog = true)
    {mc : MainCode} (hmain : Spike.Lib.A64.Rt.mainUIn prog mc = true) {Post : Ctl → BitVec 64 → Prop} {c0 : Ctl}
    (hC0 : CFacts Λ lbl c0) (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc)
    (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int} {D : Int} {ZU : Int64}
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK) (hL : mc.Z.toInt ≤ L) (hL8 : L % 8 = 0)
    (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (UInt64.ofBitVec tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v, UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' ms exe endPc (swR v (-L) 0)
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)) :
    SwUW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' exe endPc R (fun m => F m ∧ StackM rS m) ms rS
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
        (fun _ h => h.2)
    · exact Spike.Lib.A64.Rt.blkW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      exact MainUW.dt (Spike.Lib.A64.Rt.mainUW_gen hI hmain hC0 hPost hph hok h16 (by show -L ≤ _; omega)
        (Int.le_refl _) (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hZ16 hZ hk hmr
        (fun _ h => h.1.2) hsub hfit (fun _ h => h.2))
    · exact Spike.Lib.A64.Rt.mainUW_ofFalse fun _ h => hv h.1.1

end Dt

/-! ## The user `main` after the switch -/

section Sw

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` in the new stack's region** (`swUW_gen_dt`'s `hU` at
the post `UPost`, for every value `v` of the new `sp`): `userCallW_main` in
`swR v (-L) 0` under `swFSL` (vacuous off `top`), the limit word unmapped
and the words of `rS` off the callee's region from the frame condition, for
a region of depth `L` holding the caller's frame `Z` and the callee's `D`. -/
theorem userCallW_sw {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx} {r : Scc.Lower.Inv.Res}
    {fn entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC prog cx fn entry = true) (hr : Scc.Lower.Inv.lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn prog cx entry 0 r.insts r.ret = true)
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isaLSE2} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64}
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
      (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v) fn Z D (Int64.ofInt cx.frame)
      (UPost [d] lbl Spike.Lib.A64Consumer.c0) ra Spike.Lib.A64Consumer.c0 (UInt64.ofBitVec tcb) := fun v =>
  userCallW_main hd hf h1 h16 hpro hr hbody hI hD hD8 hphB hphP hC0 hmr (fun _ h => h.1.2) hsub hfit
    (fun m h hcc => by
      obtain ⟨⟨rfl, -⟩, hso⟩ := h
      have hR8 : (swR v (-L) 0).base.toNat % 8 = 0 := by show v.toNat % 8 = 0; omega
      exact stackOff_callee hok hR8 (by show (-L) % 8 = 0; omega) rfl (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by omega) hso hcc)
    hab hprog hphs himm hrel htk hk hKex hms hK hwr

end Sw

end Spike.Lib.LowerA64
