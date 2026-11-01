/-
**`HMidPAH` from `h1`'s open premises at one ghost of the box** (AArch64,
`hatA`, H1A; the hello twin of
`Spike/Lib/A64WakeH1A.lean`'s `H1GA`/`hMidPA_of`): every field of
`HelloHatA.HMidPAH` from the ghost's open facts `H1GAH`, the callee's `ti`
by `HelloTi2Hat.hti_H`.

`hti_H`'s premises split three ways: the layout's (`hp`, `hlo`, `hlab`,
`hsite`, `hΛ`, `hs`, `hro`, `hsub`), the second TCB's words and the counters
off the arena (`hmF`, `hnoF`, `hoffT`, `hoffL`, `hoffX`) and the refusals'
(`hcl`, `hCl`) are `hMidPAH_of`'s; `BoxPureH` gives the box's base and
bounds (`hbase`, `hRs`); the source at the clone gives `hSctl`
(`sctl_SBH`: at `spawnTermH` no frame step); the rest, per ghost, is
`H1GAH`'s.

- `frameRun_spawnH`, `spawnSrcH_ctl`, `sctl_SBH`: main's source at
  `spawnTermH` takes no frame step, so it is no `ret` and its runs are well
  formed (wake's `WakeSrcCtl.frameRun_spawn`, `spawnSrc_ctl`).
- `H1GAH`: `h1`'s open premises at one ghost (wake's `H1GA`).
- `hMidPAH_of`: `HMidPAH` from `BoxPureH` and `H1GAH` (wake's `hMidPA_of`).
- `hmid_h1AH`: `HelloHatA.hmid_boxAH` at `G := H1GAH` (the second stack's
  fit from `hsub`).

`WSH`'s arena `ar`, debts `Dt`, refusal `Cw`, contexts `Ctx`, sizes `lsize`
and main frame `frM` stay free (the root picks them). No absolute address
appears in this file.
-/
import Spike.Lib.A64HelloTi2Hat
import Spike.Lib.A64HelloTi2HatO
import Spike.Lib.A64HelloW2Weak

namespace Spike.Lib.HelloH1A

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.HelloWc (WcMainWH FrMGH rNH ResCtxH TcbCtxH wcNCH tcb2QH tH rARH)
open Spike.Lib.A64.HelloPh.WcSp6 (wcNSH)
open Spike.Lib.A64.Flow.WakeWc (MidG kOf tiQ)
open Spike.Lib.A64.Flow.Ret0 (CallerCells StackM)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.Rt (TcbOkGA hdrA RuntimeLayout TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResOkA ReserveW)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.HelloHMid (BoxPureH BoxMH SBH QBH CloneMidH)
open Spike.Lib.HelloHatA (HMidPAH)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH spawnTermH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.HelloPh.Ti2 (X0TH SlotPH SlotSlH)
open Spike.Lib.A64.WakePh (lo)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)

/-! ## The source at the clone -/

/-- **A control at `spawnTermH` takes no frame step** at no frames: the spawn
is a configuration step, no thread step, no call (wake's
`WakeSrcCtl.frameRun_spawn`). -/
theorem frameRun_spawnH {p : Prog} {c : Ctl} {q : Ctl × List TermRun.Frame}
    (ht : c.term = spawnTermH) (h : FrameRun p (c, []) q) : q = (c, []) := by
  cases h with
  | refl => rfl
  | step hs _ =>
    exfalso
    cases hs with
    | loc h =>
      have := h.2 { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
        { term := c.term, env := c.env } rfl rfl rfl rfl
      simp [TermRun.tstep, ht, spawnTermH, TermRun.evalOp] at this
    | call hc => rw [ht] at hc; simp [spawnTermH] at hc

/-- **The source premise at `SpawnSrcH`**: not at a `ret`, its runs well
formed, vacuously (wake's `WakeSrcCtl.spawnSrc_ctl`). -/
theorem spawnSrcH_ctl {p : Prog} {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {c : Ctl}
    (h : SpawnSrcH l ws c) :
    (∀ a, c.term ≠ .ret a) ∧ RunWf p c [] := by
  have ht := h.1
  refine ⟨fun a e => (by rw [ht] at e; simp [spawnTermH] at e), ⟨?_, ?_⟩⟩
  · intro c' fs' hr x a e ty w hc
    cases frameRun_spawnH ht hr
    rcases hc with hc | ⟨b, hc⟩ <;> rw [ht] at hc <;> simp [spawnTermH] at hc
  · intro c' fs' hr x a τ e hc
    cases frameRun_spawnH ht hr
    rw [ht] at hc; simp [spawnTermH] at hc

/-- **`hti_H`'s `hSctl`** at the source at the clone (`SBH`). -/
theorem sctl_SBH {p : Prog} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word} :
    ∀ c0 cA, MidG (SBH l b ws) c0 cA → (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [] :=
  fun _ _ ⟨_, _, ⟨_, _, h⟩, _⟩ => spawnSrcH_ctl h

/-! ## The open premises at one ghost -/

/-- **`h1`'s open premises at one ghost of the box** (`R`, `F`, `J1`, `tp`)
with the callee's take, inside the level `W`, its fence's extra `X`, the
clone's extra `Wc`, under `ms`, for the source `p`, the placement `lbl`,
the box's label `l` at `b` with the slice's words `ws`; `WSH`'s parameters `a`, `ar`, `Dt`, `Cw`,
`Ctx`, `lsize`, `frM`: `HMidPAH`'s fields but `ti`, and `hti_H`'s per-ghost
premises (wake's `H1GA`). -/
structure H1GAH (L : RuntimeLayout) (W X : FragS isaLSE2) (Wc : Frag isaLSE2)
    (ms : List TermRun.Frame → MemSide isaLSE2) (p : Prog) (lbl : Lbl) (l : WeakMem.AllocLabel) (b : Nat)
    (ws : List TermRun.Word) (a : BitVec 64) (ar : Arena) (Dt Cw : State → Prop) (Ctx : FragS isaLSE2) (lsize : Lsize)
    (frM : Ctl → TermRun.Frame) (R : Region) (F : MachineData → Prop) (J1 : AS → Ctl → Prop) (tp : UInt64) :
    Prop where
  /-- `HMidPAH.wcWf`. -/
  wcWf : WcMainWH (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc R F F (tpXa (ms []) tp) J1 (SBH l b ws)
    (QBH l b ws)
  /-- `HMidPAH.res`. -/
  res : ∀ g : Reserve.G × Ctl, g.1.ra = (L.lab ".L22_wc_main.sp3").toBitVec →
    ∀ nd, ReserveW (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (rARH R)
      (fun m => F m ∧ CallerCells R (-144) (-48) 0 m ∧ ResCtxH L.lab R
        (rNH (tpXa (ms []) tp) L.lab J1 (SBH l b ws) (QBH l b ws) .call).J g m) ⟨g.1, 0#64, g.2⟩ nd
  /-- `HMidPAH.tcb`. -/
  tcb : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ g : Ret0.AllocTcb.G, g.ra = (L.lab ".L22_wc_main.sp4").toBitVec →
    ∀ nd, TcbWG (fun s c => W s c []) (fun _ _ => False) L.exe L.endPc (R.callee (-144) (-192) 0)
      (fun mm => F mm ∧ CallerCells R (-144) (-192) 0 mm ∧ TcbCtxH L.lab R (wcNCH L.lab c0 sl me cA fr).J c0 g mm)
      (tcb2QH g c0) nd
  /-- `HMidPAH.resA`. -/
  resA : ∀ g : Reserve.G × Ctl, ResOkA (ms []) F L.exe L.endPc (rARH R) F ⟨g.1, 0#64, g.2⟩
  /-- `HMidPAH.hdrA`. -/
  hdrA : ∀ c0 g, Ret0.StOk (ms []) F L.exe L.endPc (hdrA L.lab (tcb2QH g c0)) ((tcb2QH g c0).h ||| 1#64 <<< 36)
  /-- `HMidPAH.tcbA`. -/
  tcbA : ∀ c0 g, TcbOkGA (ms []) F L.exe L.endPc (R.callee (-144) (-192) 0) F (tcb2QH g c0)
  /-- `HMidPAH.tid`. -/
  tid : (ms []).rt (tH L.lab + 56#64).toNat ∧ (ms []).mp ⟨tH L.lab + 56#64, 8⟩ true ∧
    (ms []).G ⟨tH L.lab + 56#64, 8⟩ ((1#64).setWidth 128) ∧
    ∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none
  /-- `HMidPAH.wcl`. -/
  wcl : ∀ s c sl me cA fr, At L.exe L.endPc R F (wcNSH L.lab c (tH L.lab) (kOf L.lab) sl me cA fr) s c →
    SpawnSrcH l ws c → cA.toNat = b → FrMGH J1 fr sl me → StackM (r1Of L.lab) s.st.1 → W s c [] ∧ Wc s c
  /-- `HMidPAH.hi80`. -/
  hi80 : R.hi ≤ 80
  /-- `HMidPAH.fcl`. -/
  fcl : ∀ m pm, F m → F (Ret0.takeMem pm (r1Of L.lab) m)
  /-- `HMidPAH.fcg`. -/
  fcg : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m'
  /-- `R`'s bounds 8-aligned (`hti_H`'s `hR8`). -/
  hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0
  /-- The level lift from `WSH` at main's frame, at a state writing off the arena (`HelloTi2HatO.hti_HO`'s `hWX`;
  the segment supplies the writes off the arena, `Ti2OffW.ti2_WSH_off`). -/
  hWX : ∀ c0 cA, MidG (SBH l b ws) c0 cA → ∀ s c,
    WSH L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.A64.HelloW2.OffW ar s →
      W s c [] ∧ X s c []
  /-- `c0` placed at main's slots, the box's cell's, main's id's and the slice's (`hti_H`'s `hpl`). -/
  hpl : ∀ c0 sl me cA fr, MidG (SBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
    SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
    Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 []
  /-- `F` inside the runtime's frame (`hti_H`'s `hFr`). -/
  hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m
  /-- The second TCB's words unmapped under `F` (`hti_H`'s `hunF`). -/
  hunF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none
  /-- Main's stack off `R` under `F` (`hti_H`'s `hF0`). -/
  hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) R m
  /-- The thread init's fields (`hti_H`'s `hfld`). -/
  hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
    Ret0.StOk (ms []) F L.exe L.endPc (tH L.lab + BitVec.ofNat 64 e.1) e.2
  /-- The take's facts (`hti_H`'s `htk`). -/
  htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
    R' = R.callee (-144) (-256) 0 → ∀ (g : Ret0.ThreadInit.G) (g' : Ret0.StackTake.G),
    Spike.Lib.A64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48) (-208) 0) F'
      (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')

/-- **`HMidPAH` from `H1GAH`** at a ghost of `BoxPureH`, given the layout's
facts, the second TCB's words, the counters off the arena and the refusals'
(wake's `hMidPA_of`). -/
theorem hMidPAH_of {L : RuntimeLayout} {W X : FragS isaLSE2} {Wc : Frag isaLSE2}
    {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog} {lbl : Lbl} {Cl : State → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop}
    {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : Ctl → TermRun.Frame} {F0 : MachineData → Prop}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {tp : UInt64}
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hcl : ∀ s, Cw s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hs : Spike.Lib.A64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
      (⟨b, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2bH L a j)
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hB : BoxPureH L F0 n R F J1 tp) (hG : H1GAH L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM R F J1 tp) :
    HMidPAH L W X Wc ms p lbl Cl l b ws R F J1 tp := by
  obtain ⟨-, -, -, hRlo, hhi, hbase, -⟩ := hB
  exact ⟨hG.wcWf, hG.res, hG.tcb, hG.resA, hG.hdrA, hG.tcbA, hG.tid, hG.hi80, hG.fcl, hG.fcg,
    Spike.Lib.HelloTi2HatO.hti_HO hp hlo hlab hsite hΛ hcl hCl hG.hWX hs hro sctl_SBH hG.hpl hG.hFr hmF
      hG.hunF hnoF hoffT hoffL hoffX hbase ⟨hRlo, hhi⟩ hG.hR8 hsub hG.hF0 hG.hfld hG.htk, hG.wcl⟩

/-- **`hmid` at `l`, `b`, `n` with the callee's take, at `G := H1GAH`**:
`HelloHatA.hmid_boxAH` with `hP` by `hMidPAH_of` and the second stack's
fit from `hsub`. -/
theorem hmid_h1AH {L : RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop} {W X : FragS isaLSE2}
    {Wc : Frag isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {p : Prog} {lbl : Lbl} {Cl : State → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {ws : List TermRun.Word} {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop}
    {Ctx : FragS isaLSE2} {lsize : Lsize} {frM : Ctl → TermRun.Frame}
    (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hcl : ∀ s, Cw s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hs : Spike.Lib.A64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true)
    (hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
      (⟨b, 8⟩, w) ∉ Spike.Lib.A64.HelloPh.own2bH L a j)
    (hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hpub : (ms []).pub)
    (hX : ∀ s c, pcOf s ≠ clonePcH L → pcOf s ≠ (L.lab siteL).toBitVec.toNat → X s c [])
    (hXr : ∀ s c, W s c [] → X s c [] → s.st.2 = L.lab siteL →
      Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = r1Of L.lab)
    (hokb : ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB ms0 L.lab → q.OKB (ms []) L.lab)
    (hg : (ms []).heap = ms0.heap ∧ (ms []).cells = ms0.cells ∧ (ms []).off = ms0.off ∧
      (ms []).units = ms0.units) :
    SegWS (fun s c fs => W s c fs ∧ X s c fs) (TakeCKS (L.lab siteL) Cl) p lbl ms
      (fun s c fs => BoxMH L ms0 F0 (H1GAH L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM) l b ws n s c ∧
        A64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L F0 (H1GAH L W X Wc ms p lbl l b ws a ar Dt Cw Ctx lsize frM) W Wc l b ws n) :=
  Spike.Lib.HelloHatA.hmid_boxAH hp hK hpub hCl hX hXr (Spike.Lib.A64.Rt.fitS_of_sub L hsub) hokb hg
    fun _ _ _ _ hB hG => hMidPAH_of hp hlo hlab hsite hΛ hcl hCl hs hro hsub hmF hnoF hoffT hoffL hoffX hB hG

end Spike.Lib.HelloH1A

/-- info: 'Spike.Lib.HelloH1A.frameRun_spawnH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH1A.frameRun_spawnH

/-- info: 'Spike.Lib.HelloH1A.spawnSrcH_ctl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH1A.spawnSrcH_ctl

/-- info: 'Spike.Lib.HelloH1A.sctl_SBH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH1A.sctl_SBH

/-- info: 'Spike.Lib.HelloH1A.hMidPAH_of' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH1A.hMidPAH_of

/-- info: 'Spike.Lib.HelloH1A.hmid_h1AH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH1A.hmid_h1AH
