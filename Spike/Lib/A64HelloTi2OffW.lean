/-
**The second `scc_rt_thread_init` call writes off the arena** (AArch64): the per-state fact
`HelloW2.OffW ar s` at every node of hello's second thread-init call, conjoined to `StartTi.ti2_WSH`'s level
`WSH`, so that the level lift at the clone (`H1GAH.hWX`'s `OffW` antecedent) is fed by the segment itself and no
root field has to assert it.

`WSH`'s arena conjunct (`WakeWf.Wf`'s `ArenaWr`) says every write off the counter is `ArenaW` at the level's
placement and sizes or is in the context; `ti2_WSH` holds at any context and sizes. At the empty context and the
sizes `fun _ => 0` the context disjunct is gone, a placed label has no cells (`lrange` empty), and the allocation
disjuncts need a held counter, which the ti nodes' control `c0` (main's source at the spawn, `SpawnSrcH`) does not
hold: what is left of `ArenaW` is "off the arena"; the counter is not written because the context is empty.

- `offW_of_wsh`: `OffW` from `WSH` at the empty context and zero sizes, at a control holding nothing.
- `ti2_offW`: `ti2_WSH` at that context and sizes, read as `TiW (fun s _ => OffW ar s)`.
- `ti2_WSH_off`: `ti2_WSH`'s obligations inside `WSH ∧ OffW` (`TiW.imp`).
- `offW_pool`: the real pool is off the real arena (non-vacuity of the conjunct's discharge at the root: the
  frames' and the TCB's words the call writes lie in the stack pool and in `pinned`, both disjoint from the heap
  and the counter's `.data` word).
-/
import Spike.Lib.A64HelloTi2W
import Spike.Lib.A64HelloW2Weak
import Spike.Lib.LowerA64.StartEW2
import Spike.Lib.A64WakeTi2C0
import Spike.Lib.A64WakeWcMidW
import Spike.Lib.A64HelloHrdArena

namespace Spike.Lib.A64.HelloPh.Ti2OffW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.Ret0 (TiG TiW StackM TI)
open Spike.Lib (Arena FragS Ctl)
open Spike.Lib.A64.WakePh.Ti2 (BandP)
open Spike.Lib.A64.HelloW2 (OffW)
open Spike.Lib.A64.HelloPh.StartTi (ti2_WSH)

/-- **`OffW` from `WSH` at the empty context and zero sizes** (module doc), at a control holding nothing (`hh`):
the counter is not written (`Wf`'s counter row at the empty context), and `ArenaW` at zero sizes with no held
counter is "off the arena". -/
theorem offW_of_wsh {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {lbl : Lbl}
    {frM : TermRun.Frame} {X0 : State → Prop} {s : State} {c : Ctl}
    (h : WSH L a ar p Dt Cl (fun _ _ _ => False) lbl (fun _ => 0) frM X0 s c) (hh : c.hold = none) : OffW ar s := by
  obtain ⟨-, -, -, -, -, -, -, -, hAW, hctr, -, -⟩ := h
  intro Lw hw
  have hne : Lw ≠ ar.ctrLoc := fun e => hctr (e ▸ hw)
  refine ⟨hne, ?_⟩
  rcases hAW c [] (Spike.Lib.FrameRun.refl _) Lw hw hne with h | ⟨h, -⟩
  · rcases h with h | h | ⟨l, b, -, hc⟩ | ⟨old, x, aa, τ, e, ta, ws, k, hhold, -⟩ | ⟨-, old, x, aa, e, ty, ws, hhold, -⟩
    · exact absurd h hne
    · exact h
    · simp only [Scc.Sem.lrange, Range.contains] at hc; omega
    · rw [hh] at hhold; cases hhold
    · rw [hh] at hhold; cases hhold
  · exact h.elim

/-! ## `Ti2C0.tiW_c0` reading the dummy control only -/

section C0

open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW takeNG tiN)
open Spike.Lib.A64.WakePh.WcW (blkW_mapC nodeW_mapC)
open Spike.Lib.A64.WakePh.Ti2C0 (takeJ_c0 tiJ_c0)

variable {W W' : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F M P : MachineData → Prop}

/-- **`Ti2C0.takeW_c0` with `hW` read at the dummy control only**: `W` at `c0'` gives `W'` at every control. -/
theorem takeW_c0' {q : TakeG} {c0' : Ctl} (hW : ∀ s c, W s c0' → W' s c)
    (h : ∀ i, TakeW W K exe endPc R F M { q with c0 := c0' } i P) : ∀ i, TakeW W' K exe endPc R F M q i P := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  have hL : ∀ {l' : Label} {lab' : Label → Int64} {P P' : Spike.Lib.A64.Flow.AS → Ctl → Prop},
      (∀ σ c, P σ c → P' σ c0') → ∀ σ c,
      (∃ σ0, P σ0 c ∧ σ = (Spike.Lib.A64.Flow.SI.adrp .X9 l').step lab' σ0) →
      ∃ σ0, P' σ0 c0' ∧ σ = (Spike.Lib.A64.Flow.SI.adrp .X9 l').step lab' σ0 :=
    fun hP σ c ⟨σ0, h1, h2⟩ => ⟨σ0, hP σ0 c h1, h2⟩
  cases i <;> dsimp only [TakeW] at hi ⊢
  case site =>
    exact fun s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ => hW s c (hi s c0' ⟨he, hn, hd, hp, σ, hA, hF, takeJ_c0 hJ⟩)
  case d0 | d7 | d14 | b0 | b6 | ok0 =>
    exact ⟨hN hi.1 rfl rfl (fun _ _ => takeJ_c0), hN hi.2 rfl rfl (hL fun _ _ => takeJ_c0)⟩
  case swp | ldn | unl | nxt => exact hN hi rfl rfl (fun _ _ => takeJ_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => takeJ_c0)

/-- **`Ti2C0.tiW_c0` with `hW` read at the dummy control only.** -/
theorem tiW_c0' {q : TiG} {c0' : Ctl} (hW : ∀ s c, W s c0' → W' s c)
    (h : ∀ i, TiW W K exe endPc R F M { q with c0 := c0' } i P) : ∀ i, TiW W' K exe endPc R F M q i P := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc →
      n'.o = n.o → (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c h⟩
  cases i <;> dsimp only [TiW] at hi ⊢
  case call => exact fun g hg j => takeW_c0' hW (hi g hg) j
  case st0 | st1 | st2 | st3 | st4 | st5 => exact hN hi rfl rfl (fun _ _ => tiJ_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => tiJ_c0)

/-- **`scc_rt_stack_take`'s obligations at two levels combine** (`WcMidW`'s `blkW_and`/`nodeW_and`, the first's
outside move). -/
theorem takeW_and {W₂ : Spike.Lib.Frag isaLSE2} {K₂ : State → State → Prop} {q : TakeG} {i : TK}
    (h₁ : TakeW W K exe endPc R F M q i P) (h₂ : TakeW W₂ K₂ exe endPc R F M q i P) :
    TakeW (fun s c => W s c ∧ W₂ s c) K exe endPc R F M q i P := by
  cases i <;> dsimp only [TakeW] at h₁ h₂ ⊢ <;>
    first
    | exact Spike.Lib.A64.Flow.WakeWc.blkW_and h₁ h₂
    | exact Spike.Lib.A64.Flow.WakeWc.nodeW_and h₁ h₂
    | exact ⟨Spike.Lib.A64.Flow.WakeWc.nodeW_and h₁.1 h₂.1, Spike.Lib.A64.Flow.WakeWc.nodeW_and h₁.2 h₂.2⟩
    | exact fun s c hA => ⟨h₁ s c hA, h₂ s c hA⟩

/-- **`scc_rt_thread_init`'s obligations at two levels combine.** -/
theorem tiW_and {W₂ : Spike.Lib.Frag isaLSE2} {K₂ : State → State → Prop} {q : TiG} {i : TI}
    (h₁ : TiW W K exe endPc R F M q i P) (h₂ : TiW W₂ K₂ exe endPc R F M q i P) :
    TiW (fun s c => W s c ∧ W₂ s c) K exe endPc R F M q i P := by
  cases i <;> dsimp only [TiW] at h₁ h₂ ⊢ <;>
    first
    | exact Spike.Lib.A64.Flow.WakeWc.blkW_and h₁ h₂
    | exact Spike.Lib.A64.Flow.WakeWc.nodeW_and h₁ h₂
    | exact fun g hg j => takeW_and (h₁ g hg j) (h₂ g hg j)

end C0

section Gen

variable {P : MachineData → Prop}
variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [])
  (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
  (hX0 : ∀ s, Spike.Lib.A64.WakePh.inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbdI : BandP L R (-256))

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbdI

/-- **The second thread init's node obligations inside `OffW`** (`ti2_WSH` at the empty context and zero sizes,
`offW_of_wsh`; its premises `ti2_WSH`'s but the control's hold, `hh`). -/
theorem ti2_offW (Dt : State → Prop) (frM : TermRun.Frame) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : Spike.Lib.A64.WakePh.WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TiG) (hh : c0.hold = none)
    (hmF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb,
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨b, 8⟩ = true)
    (hunF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ j w, (⟨b, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2bH L a j)
    (hra : q.g.ra = (L.lab ".L22_wc_main.sp6").toBitVec)
    (hrS : rS = ⟨(Spike.Lib.A64.Flow.Ret0.stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hSMt : Spike.Lib.A64.Flow.FStable (R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      Spike.Lib.A64.Flow.Ret0.CallerCells R Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0 s.st.1 →
      (∀ k, (R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0).Off k →
        (Mem.loadInt s.st.1.dmem ((R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0).addr k) 8).isSome) →
      X0 s) :
    ∀ i, TiW (fun s _ => OffW ar s) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F (StackM rS) q i P := by
  exact tiW_c0' (c0' := c0) (fun _ _ hw => offW_of_wsh hw hh)
    (ti2_WSH (Ctx := fun _ _ _ => False) (lsize := fun _ => 0) (Dt := Dt) (frM := frM) hp hlo hlab hsite hcl hc0
      hpl0 hPl hX0 hbdI hΛ hs hro hR hal hRlo hhi hFr { q with c0 := c0 } rfl hmF hunF hnoF hra hrS hsub hSM hSMt
      hoffT hoffL hoffX hXs)

/-- **`ti2_WSH`'s obligations inside `WSH ∧ OffW`** (`TiW.imp` of `ti2_WSH` and `ti2_offW`). -/
theorem ti2_WSH_off (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : Spike.Lib.A64.WakePh.WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (q : TiG) (hq : q.c0 = c0) (hh : c0.hold = none)
    (hmF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb,
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨b, 8⟩ = true)
    (hunF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb, ∀ j w, (⟨b, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2bH L a j)
    (hra : q.g.ra = (L.lab ".L22_wc_main.sp6").toBitVec)
    (hrS : rS = ⟨(Spike.Lib.A64.Flow.Ret0.stacksA L.lab + q.k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS))
    (hSMt : Spike.Lib.A64.Flow.FStable (R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (StackM rS))
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs q.tcb,
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → P s.st.1 →
      Spike.Lib.A64.Flow.Ret0.CallerCells R Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0 s.st.1 →
      (∀ k, (R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0).Off k →
        (Mem.loadInt s.st.1.dmem ((R.callee Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0).addr k) 8).isSome) →
      X0 s) :
    ∀ i, TiW (fun s c => WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c ∧ OffW ar s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (StackM rS) q i P := by
  intro i
  have hO := ti2_offW hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbdI Dt frM hΛ hs hro hR hal hRlo hhi hFr q hh hmF hunF hnoF
    hra hrS hsub hSM hSMt hoffT hoffL hoffX hXs i
  have hW := ti2_WSH (Ctx := Ctx) (lsize := lsize) (Dt := Dt) (frM := frM) hp hlo hlab hsite hcl hc0 hpl0 hPl hX0
    hbdI hΛ hs hro hR hal hRlo hhi hFr q hq hmF hunF hnoF hra hrS hsub hSM hSMt hoffT hoffL hoffX hXs i
  exact tiW_and hW hO

end Gen

/-! ## The real pool is off the real arena (non-vacuity) -/

section Pool

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

/-- **A word in the stack pool is off `arW`'s cells and its counter** at the root's layout: the arena is inside
`.heap` (`arOf_sub`), the counter in `.data` (`ctr_item_of_placeW`), both disjoint from the pool (`WF.disjoint`).
The frames the thread init and the take write lie in the pool (`hti_H`'s `hsub`, `bandP_boxH`), the TCB's words,
the lock and the next cursor are `hoffT`/`hoffL`/`hoffX` (`HrdArena.offH_own`, `RootPlug.hoffT_H`): this is the
discharge `OffW` abstracts at every write of the call. -/
theorem offW_pool (hc : Spike.Lib.A64.Rt.CtrZ o) :
    ∀ a : BitVec 64, (Ly).Λ.stackPool.contains a.toNat →
      ¬ ((AR).heap ≤ a.toNat ∧ a.toNat < (AR).heap + 16 * (AR).cells) ∧ (⟨a, 8⟩ : Loc) ≠ (AR).ctrLoc := by
  intro a ha
  have hs : (Scc.Sem.Range.mk (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap (16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells)).Sub
      (Ly).Λ.heap := Spike.Lib.A64.Rt.ArenaW.arOf_sub (Spike.Lib.PlaceW.link i hpw)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hH := hwf.disjoint.2.2.2.2.2.1
  have hD := hwf.disjoint.2.2.2.2.1
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link i hpw) hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hct : (AR).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  change (Ly).Λ.stackPool.contains a.toNat at ha
  refine ⟨?_, fun h => ?_⟩
  · change ¬ ((Spike.Lib.A64.Rt.arOf (Ly).Λ).heap ≤ a.toNat ∧
      a.toNat < (Spike.Lib.A64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).cells)
    simp only [Scc.Sem.Range.Sub, Scc.Sem.Range.Disjoint, Scc.Sem.Range.contains] at hs hH ha
    omega
  · have ha' : a = BitVec.ofNat 64 (AR).ctr := congrArg Loc.addr h
    have := congrArg BitVec.toNat ha'
    rw [BitVec.toNat_ofNat, hct, Nat.mod_eq_of_lt (by omega)] at this
    simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.contains] at hD ha
    omega

end Pool

/-- **`offW_of_wsh`'s hold premise at the ti nodes' control**: main's source at the spawn (`SpawnSrcH`, the control
`MidG (SBH …)` pins) holds nothing. -/
example {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {c : Ctl}
    (h : Spike.Lib.HelloMainPreSrc.SpawnSrcH l ws c) : c.hold = none := h.2.1

end Spike.Lib.A64.HelloPh.Ti2OffW

/-- info: 'Spike.Lib.A64.HelloPh.Ti2OffW.offW_of_wsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2OffW.offW_of_wsh

/-- info: 'Spike.Lib.A64.HelloPh.Ti2OffW.ti2_offW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2OffW.ti2_offW

/-- info: 'Spike.Lib.A64.HelloPh.Ti2OffW.ti2_WSH_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2OffW.ti2_WSH_off

/-- info: 'Spike.Lib.A64.HelloPh.Ti2OffW.offW_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2OffW.offW_pool
