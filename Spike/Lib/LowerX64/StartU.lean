/-
**The start's switch and `scc_rt_main` with the user `main`, inside the
consumer's facts with the overflow stub's write tail** (x86-64): the pieces
of `startU_segW` (`Spike/Lib/Rt/X64Segs.lean`) that the user `main` feeds,
at `W := SFacts … Dt` (the write tail `Dt` live: the overflow stub writes
inside the user's callee region). The twin of
`Spike/Lib/LowerA64/StartU.lean`.

- `uPost_exit`: `startU_segW`'s `hexit` at the post `UPost` under the
  placement's memory side (`msOf`): a control at `main`'s `ret` of the
  number in `%rdi` is `main`'s exit with that number mod 256 (`MainExit`).
- `MainUW.dt`: `scc_rt_main`'s own obligations at `Dt = False` hold at any
  `Dt` (`SFacts.dt_mono`).
- `swUW_gen_dt`: `swUW_gen` (`Spike/Lib/Rt/X64RtMainU.lean`) with the user
  function's interface and the conclusion at `SFacts … Dt`.
- `userCallW_sw`: the user `main`'s interface (`userCallW_main`,
  `Spike/Lib/LowerX64/AbortCall.lean`) in `scc_rt_main`'s callee region
  after the switch (`swR`, `swFSL`), for every value of the new `%rsp`.
- `swL`, `swL_ok`: the switch region's depth as a function of the frame
  (`fr.size + 104`: `scc_rt_main`'s frame of `32` with its return address
  and saved `%rbp`, and the user's depth `fr.size + 48`), inside the first
  stack for every `MainSeg` frame (`≤ 4096`).

Where x86-64 differs from AArch64: the user function's region is
`scc_rt_main`'s callee region inside the switch's (`SwUW.user` quantifies
over its frame condition, with the caller's cells); the switch region is
8-aligned; `startU_segW`'s depth bound is `8 + 8 + Z + 8 + D ≤ L`.
-/
import Spike.Lib.LowerX64.AbortCall
import Spike.Lib.Rt.X64RtMainU

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Sem (Marks Range ValRep)
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl Lsize blkPh msOf Placed K0)
open Spike.Lib.X64.Rt (InstOk UserCallW MainCode MainUW SwUW swFSL stackOff_callee)
open Spike.Lib.X64.Flow.Ret0 (StackOff StackM CallerCells limA tpOf)
open Spike.Lib.X64.StubW (abortPhOk)

/-! ## `main`'s exit -/

/-- **`main`'s exit at the post `UPost`** (`startU_segW`'s `hexit`), under
the placement's memory side: from the start `c0` a local run reaches
`ret a` of a number represented by `%rdi` (`RetV`), placed in `%rdi`, whose
return is the exit with the number mod 256. -/
theorem uPost_exit {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Own} {lbl : Lbl} {ls0 : Lsize} {ms : MemSide isa} (hms : ms = msOf Λ μ rd G own lbl ls0)
    {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (v : BitVec 64), UPost p lbl c0 c v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExit p ms s c v.toNat := by
  subst hms
  rintro R' F' s c v ⟨rfl, c', hr, a, t, w, hta, -, hev, ⟨n, hn⟩, hv⟩ ⟨-, -, -, -, σ, hA, -, hx⟩ -
  have hx0 : Scc.Sem.X64.regVal s (.r .rdi) = v := by
    show s.st.1.regs.rdi.toBitVec = v
    rw [hA.regs]; exact hx
  refine ⟨c', hr, ?_, ?_⟩
  · show Placed Λ lbl s c'
    cases a with
    | var y =>
      refine ⟨fun x k => if x = y ∧ k = 0 then some (.one (.reg (.r .rdi))) else none, ?_, ?_, ?_⟩
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
        exact ⟨.one (.reg (.r .rdi)), by simp⟩
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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

private theorem dtJ {Dt : State → Prop} {J : AS → Ctl → Prop} :
    ∀ σ c, J σ c → ∃ c', J σ c' ∧ ∀ s, SFacts Λ μ own rS Tk lbl s c' → SFacts Λ μ own rS Tk lbl s c Dt :=
  fun _ c h => ⟨c, h, fun _ hs => hs.dt_mono fun _ h => h.elim⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_main`'s own obligations at any write tail.** -/
theorem MainUW.dt {Dt : State → Prop} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
    {mc : MainCode} {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.X64.Flow.Ret0.MainG}
    (h : MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms mc Post g) :
    MainUW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F ms mc Post g :=
  ⟨XProW.mapC h.pro dtJ, BlkW.mapC rfl rfl h.call dtJ,
    ⟨BlkW.mapC rfl rfl h.exit.w0 dtJ, NodeW.mapC rfl rfl h.exit.w1 dtJ⟩⟩

set_option maxHeartbeats 800000 in
open Spike.Lib.X64.Rt.MainU in
/-- **`swUW_gen` at a live write tail**: the switch's and `scc_rt_main`'s
states inside `SFacts … Dt`, the user function's interface there (`hU`);
the premises otherwise `swUW_gen`'s. -/
theorem swUW_gen_dt {p : Prog} {lbl' : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {Dt : State → Prop}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph)
    (hin : Spike.Lib.X64.Flow.Ret0.startTailIn cells = true) {mc : MainCode}
    (hmain : Spike.Lib.X64.Rt.mainUIn cells mc = true) {Post : Ctl → BitVec 64 → Prop} {c0 : Ctl}
    (hC0 : CFacts Λ lbl c0) (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPh okPc ph lab mc)
    (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int} {D : Int} {ZU : Int64}
    (h8 : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : mc.Z.toInt + 24 ≤ L) (hL8 : L % 8 = 0)
    (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (tpOf tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v (F' : MachineData → Prop),
      (∀ m, F' m → swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      UserCallW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' ms exe endPc
        ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' mc.fn mc.Z D ZU Post
        ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb)) :
    SwUW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K p lbl' exe endPc R (fun m => F m ∧ StackM rS m) ms rS
      tcb top c0 L mc D ZU Post := by
  have h := hin
  simp only [Spike.Lib.X64.Flow.Ret0.startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, bSw⟩, bXor⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_, hU⟩
  · refine NodeW.mapC rfl rfl ?_ dtJ
    rw [hI.labOk]
    exact Spike.Lib.X64.Rt.nodeW_reg_post (p := lab Spike.Lib.X64.Flow.Ret0.x1L + Int64.ofNat 28) hI (by rfl) bSw
      rfl rfl (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1 hsw.sw.2 hsub
  · by_cases hv : v = top
    · subst hv
      refine NodeW.mapC rfl rfl ?_ dtJ
      rw [hI.labOk]
      exact Spike.Lib.X64.Rt.nodeW_fi_postO (p := lab Spike.Lib.X64.Flow.Ret0.x1L + Int64.ofNat 31) hI bXor rfl rfl
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.xor.1 hsw.xor.2 hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) hsub (fun _ h => h.2)
    · exact Spike.Lib.X64.Rt.nodeW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      refine BlkW.mapC rfl rfl ?_ dtJ
      rw [hI.labOk]
      exact Spike.Lib.X64.Rt.blkW_postO hI bMain rfl (Spike.Lib.X64.Rt.startMain_okL (by omega)) hok
        (Int.le_refl _) (Int.le_refl _) h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main
        (fun _ _ _ k hk r => (Spike.Lib.X64Consumer.noRet_false startMain_noRet k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit (fun _ h => h.2)
    · exact Spike.Lib.X64.Rt.blkW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      have hR := Region.callee_ok (kc := -8 - 0) (lo' := 8 - L) (hi' := 8) hok (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by show _ ≤ (0 : Int); omega)
      exact MainUW.dt (Spike.Lib.X64.Rt.mainUW_gen hI hmain hC0 hPost hph hR
        (Spike.Lib.LowerX64.addr_toNat_mod8 _ h8 (by decide)) (by show 8 - L ≤ _; omega)
        (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
        hZ hZ8 hps hk hmr (fun _ h => h.1.1.2) hsub hfit
        (fun _ h => stackOff_callee hok h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
          (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by decide) h.1.2 h.2))
    · exact Spike.Lib.X64.Rt.mainUW_ofFalse fun _ h => hv h.1.1.1

end Dt

/-! ## The user `main` after the switch -/

section Sw

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

/-- **The user `main` in `scc_rt_main`'s callee region after the switch**
(`swUW_gen_dt`'s `hU` at the post `UPost`, for every value `v` of the new
`%rsp` and frame condition `F'` inside `swFSL` with the switch region's
cells outside the callee's): `userCallW_main` there (vacuous off `top`),
the limit word unmapped and the words of `rS` off the user's region from
the frame condition, for a switch region of depth `L` holding the
caller's frame `Z`, the two return addresses and saved `%rbp`s, and the
callee's `D`. -/
theorem userCallW_sw {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {fr : Scc.Emit.X64.Frame} {r : Res}
    {fn entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true) (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn cells fr entry 0 r.insts r.ret = true)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph) {Dt : State → Prop}
    {lbl : Lbl} {ms : MemSide isa} {Z : Int64} {D L : Int} {tcb top : BitVec 64} {ra : BitVec 64}
    (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (htop : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : 8 + 8 + Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hZ8 : Z.toInt % 8 = 0) (hZ : 0 ≤ Z.toInt)
    (hphB : bodyPhOk okPc ph (fun _ => false) lab cells fr entry r.insts r.ret (Int64.ofBitVec ra) = true)
    (hphP : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts Λ lbl Spike.Lib.X64Consumer.c0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA (tpOf tcb), 8⟩ = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hab : r.insts ≠ [] → blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (himm : Λ.imms = Spike.Lib.LowerNode.immsOf d)
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
    exact userCallW_main hd hf h1 hpro hr hbody hI hb8 hZ8 hD hD8 hphB hphP hC0 hmr (fun _ h => (hF' _ h).1.1.2)
      hsub hfit
      (fun _ h hc => stackOff_callee hR hb8 (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
        (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega) (by omega)
        (stackOff_callee hok htop (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
          (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by decide) (hF' _ h).1.2 (hF' _ h).2)
        hc)
      hab hprog hsysIn hphs himm hrel htk hk hKex hms hK hwr
  · intro F'' _ _ hFF _ _ _ _
    exact seg_falseW.mono_pre fun _ _ ⟨_, _, _, _, _, _, hD', _⟩ => hv (hF' _ (hFF _ hD').1).1.1.1

end Sw

/-! ## The switch region's depth -/

/-- **The switch region's depth for a user frame of `n` bytes**:
`scc_rt_main`'s frame (`32`), its return address and saved `%rbp` and the
user's return address (`24`), and the user's depth `n + 48`. -/
def swL (n : Nat) : Int := (n : Int) + 104

/-- **`swL` fits `startU_segW` and the first stack** for every `MainSeg`
frame (`fr.size ≤ 4096`, 16-aligned): the user's depth `n + 48` with
`bareMC`'s frame of `32` (`8 + 8 + 32 + 8 + (n + 48) ≤ swL n`), 8-aligned,
inside the `16384` bytes of a stack. -/
theorem swL_ok {n : Nat} (h : n ≤ 4096) (h16 : n % 16 = 0) :
    8 + 8 + Spike.Lib.X64.Rt.bareMC.Z.toInt + 8 + ((n : Int) + 48) ≤ swL n ∧ swL n % 8 = 0 ∧
      0 ≤ swL n ∧ swL n ≤ 16384 ∧ ((n : Int) + 48) % 8 = 0 := by
  have hZ : Spike.Lib.X64.Rt.bareMC.Z.toInt = 32 := by decide
  unfold swL
  omega

end Spike.Lib.LowerX64
