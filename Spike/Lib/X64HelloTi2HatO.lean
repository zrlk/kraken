/-
**`HMidPAH.ti`'s discharger with the level lift under `OffW`** (x86-64; the twin of
`Spike/Lib/A64HelloTi2HatO.lean`): `X64HelloTi2Hat.hti_H` with its `hWX` taking the writes off the arena as an
antecedent (`HelloW2.w2H_of_wsh`'s shape), fed by the segment itself (`Ti2OffW.ti2_WSPH_off`), so that no root
premise has to assert the writes off the arena. The statement and proof are `hti_H`'s but for `hWX` and the nodes'
obligations; the control's hold is the source facts' (`MidG (QBH …)`).

- `hti_HOX`: `HMidPAH.ti` from `hWX` under `OffW`, the level lift from `WSHX` (the start's level at `ownGHXW`,
  main's and the worker's TCB words owned; the nodes by `OwnTi2.ti2LH` and `TiWAtP.imp`), given the worker's TCB
  word off the counters and `a` (`hW`).

**Unlike AArch64**: as `X64HelloTi2Hat.hti_H` against `A64HelloTi2Hat.hti_H` (regions, `QBH`, `NoSetFsAt`,
`Rt.TiWAtP … x8L` with the site condition `Pz r1Of ∧ CallerCells`); the hold is `QBH`'s own conjunct (AArch64:
`SpawnSrcH`'s, under `SBH`). AArch64's `hti_HO` lifts from the start's level at `ownGH`; the root's start level
here is at `ownGHXW`, so only `hti_HOX` is stated.
-/
import Spike.Lib.X64HelloTi2Hat
import Spike.Lib.X64HelloTi2OffW

namespace Spike.Lib.X64HelloTi2HatO

section Hat

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.HelloWc (FrMGH wcNIH tH oCH)
open Spike.Lib.X64.Flow.WakeWc (MidG tiQ stOk_tpXa)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StackM CallerCells)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.KeepTP (NoSetFsAt tpXa)
open Spike.Lib.X64ConsumerA (TakeCK)
open Spike.Lib.X64Consumer (Pz Lbl Lsize)
open Spike.Lib.X64HelloHMid (QBH)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64.HelloPh.Ti2 (X0TH SlotPH SlotSlH)
open Spike.Lib.X64.HelloPh (lo WSHX)
open Scc.Sem.X64 (pcOf abi codeLabel)
open Spike.Lib.X64HelloTi2Hat (site_ne_clonePcH tiWAtP_nmAt)

set_option maxHeartbeats 3200000 in
/-- **`HMidPAH.ti` from the level lift under `OffW` at `WSHX`** (AArch64 `hti_HO` with the level lift from the start's
level at `ownGHXW`; the nodes inside `WSHX ∧ OffW` by `OwnTi2.ti2LH` and `TiWAtP.imp`, as `Ti2Hat.hti_H`): the worker's
TCB word off the counters and `a` (`hW`). -/
theorem hti_HOX {L : RuntimeLayout} {W X : FragS isa} {ms : List TermRun.Frame → MemSide isa}
    {p : Prog} {lbl : Lbl} {Cl : State → Prop} {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {tp : UInt64}
    {a : BitVec 64} {ar : Arena} {Dt Cw : State → Prop} {Ctx : FragS isa} {lsize : Lsize}
    {frM : Ctl → TermRun.Frame}
    (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hcl : ∀ s, Cw s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (hWX : ∀ c0 cA, MidG (QBH l b ws) c0 cA → ∀ s c,
      WSHX L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c → Spike.Lib.X64.HelloW2.OffW ar s →
      W s c [] ∧ X s c [])
    (hs : Spike.Lib.X64.WakePh.WSep L a)
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    (hSctl : ∀ c0 cA, MidG (QBH l b ws) c0 cA → (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c0 [])
    (hpl : ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me → ∀ s : State,
      SlotPH R b me.toNat s.st.1 ∧ SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat s.st.1 →
      Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m)
    (hmF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true)
    (hunF : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hnoF : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
      (⟨b, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2bH L a j)
    (hoffT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (tH L.lab),
      ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hbase : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -384 ∧ 8 ≤ R.hi)
    (hR8 : R.lo % 8 = 0 ∧ R.hi % 8 = 0)
    (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hF0 : ∀ m, F m → Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) R m)
    (hfld : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      Ret0.StOk (ms []) F (tH L.lab + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ (c0 : Ctl) (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) →
      R' = R.callee (-136) (-248) 8 → ∀ (g g' : Ret0.AllocTcb.G),
      Spike.Lib.X64.Rt.TakeOkA (ms []) F L.exe L.endPc (R'.callee (-48 - 0) (-200) 8) F'
        (Ret0.tiTake (tiQ (tH L.lab) c0 g) g')) :
    ∀ c0 sl me cA fr, MidG (QBH l b ws) c0 cA ∧ FrMGH J1 fr sl me →
    ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) F' →
      (∀ m, F' m → F m) → R' = R.callee (-136) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -136) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-136) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oCH mC σC ∧ (wcNIH L.lab c0 (tH L.lab) sl me cA fr).J σC c ∧
          (tiN L.lab (tiQ (tH L.lab) c0 g) .e).J (enter (-136) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -136) →
            Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW (fun s c => (W s c [] ∧ X s c []) ∧ NoSetFsAt s)
          (TakeCK (L.lab Ret0.StackTake.siteL) (r1Of L.lab) Cl) p lbl (tpXa (ms []) tp)
          (fun s c => At L.exe L.endPc R' F' (tiN L.lab (tiQ (tH L.lab) c0 g) .e) s c ∧ Pz (r1Of L.lab) s.st.1)
          (fun s c => ∃ x, At L.exe L.endPc R' F' (tiX L.lab (tiQ (tH L.lab) c0 g) x) s c ∧
            StackM (r1Of L.lab) s.st.1) := by
  intro c0 sl me cA fr hM R' F' hR hRlo hhi hF hKt hFF hR' hCC g hpre hFm
  subst hR'
  obtain ⟨l', A, ⟨-, rfl, -⟩, hcA⟩ := id hM.1
  have hbd := Spike.Lib.X64.HelloPh.Ti2.bandP_boxH hbase
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub L hsub
  have hout := Spike.Lib.X64.HelloPh.Ti2.hout_boxH (L := L) hbase
  have hRS := Spike.Lib.X64.HelloPh.Ti2.hRS_boxH (L := L) hbase
  have hrc : Spike.Lib.X64.Rt.RtCodeIn0 L.prog := hp ▸ Spike.Lib.X64.HelloPh.hello_rtCodeIn0
  have hti : Ret0.ThreadInit.threadInitInAt L.prog Spike.Lib.X64.Rt.x8L = true :=
    hp ▸ Spike.Lib.X64.HelloPh.hello_tiIn
  -- the return address `.x25`, from the caller's node
  have hra : g.ra = (L.lab ".Lwc_main.x3").toBitVec := by
    obtain ⟨σC, c, hw, -, -, -, hx, -⟩ := hpre
    exact hx.symm.trans hw.2.2.1
  -- the take's frame and `r1Of`'s stability
  have hSM := Ret0.stackM_stable hfit hout
  have hSMt : FStable ((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8) (StackM (r1Of L.lab)) := by
    refine Ret0.stackM_stable hfit fun a h8 ha ha7 => ?_
    show (a : Int) + 8 ≤ (((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8).base.toNat : Int) + -200 ∨
      (((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8).base.toNat : Int) + 8 ≤ a
    have hb' := Region.callee_base (hi' := 8) hR
      (show (R.callee (-136) (-248) 8).lo ≤ (-48 - 0) + -200 by omega)
      (by decide) (show (-48 - 0 : Int) < (R.callee (-136) (-248) 8).hi by omega)
    rcases hout a h8 ha ha7 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hal8 : R.base.toNat % 8 = 0 := by have := L.stacks_al; omega
  -- main's slots at the callee's states, for the placement
  have hPlK0 := Spike.Lib.X64.HelloPh.Ti2.slotPH_keep (L := L) hbase ⟨by omega, by omega⟩ hcA rfl fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h
    ⟨mC, σC, hA, hJ.2.2.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.2.1, hk⟩
  -- the slice's slots (`FrWH`'s `-8`, `-24`, `-32`), for the packet's words
  have hPlS := Spike.Lib.X64.HelloPh.Ti2.slotSlH_keep (L := L) (sl := sl) hbase ⟨by omega, by omega⟩ fun m' h =>
    let ⟨mC, σC, _, hA, hJ, _, hk⟩ := hFm m' h
    ⟨mC, σC, hA, hJ.2.2.2.2.1, hJ.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.1, hk⟩
  have hPlK := fun m m' h hd => And.intro (hPlK0 m m' h hd) (hPlS m m' h hd)
  -- the control's hold (`QBH`'s)
  have hh : c0.hold = none := by
    obtain ⟨_, _, ⟨-, -, -, hS, -⟩, -⟩ := hM.1
    exact hS
  -- the take site's frame condition
  let PT : MachineData → Prop := fun m => Pz (r1Of L.lab) m ∧
    CallerCells (R.callee (-136) (-248) 8) (-48 - 0) (-200) 8 m
  -- the nodes inside `WSH ∧ OffW` at `X0TH`, then at `NoSetFsAt`
  have hT := Spike.Lib.X64.HelloPh.Ti2OffW.ti2_WSPH_off (P := PT)
    (L := L) (a := a) (rS := r1Of L.lab) (ar := ar) (p := p) (Dt := Dt) (Cl := Cw)
    (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (frM := frM c0)
    (X0 := X0TH L (L.lab siteL))
    hp hlo hlab hsite hcl (hSctl c0 cA hM.1) (hpl c0 sl me cA fr hM) hPlK
    (Spike.Lib.X64.HelloPh.Ti2.x0TH_ti hlab rfl)
    (Spike.Lib.X64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hΛ hs hro hR hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (tH L.lab) c0 g) rfl hh hmF (fun a ha m h => hunF a ha m (hFF m h)) hnoF
    hra rfl hsub hSM hSMt hoffT hoffL hoffX
    (fun s hpc hr hm hP h3 => Spike.Lib.X64.HelloPh.Ti2.x0TH_sitePz (site_ne_clonePcH hlab)
      (P := fun s => CallerCells (R.callee (-136) (-248) 8) (-48 - 0) (-200) 8 s.st.1 ∧
        ∀ k, ((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8).Off k →
          (Mem.loadInt s.st.1.dmem (((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8).addr k) 8).isSome)
      (fun s _ _ hm h4 => Spike.Lib.X64.HelloPh.Ti2.owned_r0H hbase hal8 hR8 hRs (hF0 _ (hFF _ hm)) (hCC _ hm)
        h4.1 h4.2) s hpc hr hm hP.1 ⟨hP.2, h3⟩)
  -- lifted to `WSHX ∧ OffW` (`ti2LH` at the worker's TCB word), then to `NoSetFsAt`
  have htcb : (tiQ (tH L.lab) c0 g).tcb = Spike.Lib.X64HelloOwnLift.tcbWH L := by
    show Ret0.pinA L.lab + 144#64 = L.pinA + 144#64; rw [L.lab_pin]
  have hL := Spike.Lib.X64.HelloPh.OwnTi2.ti2LH (L := L) (a := a) (ar := ar) (p := p) (Dt := Dt) (Cl := Cw)
    (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (frM := frM c0) (X0 := X0TH L (L.lab siteL))
    (M := StackM (r1Of L.lab)) hp hlab hsite hs.tcb (hs.tcb_a 1 (by decide)) hW
    (Spike.Lib.X64.WakePh.Ti2.bandP_callee hbd (by decide) (by decide)) hR hRlo hhi
    (fun m h => hFr m (hFF m h)) (tiQ (tH L.lab) c0 g) htcb (fun a ha m h => hunF a ha m (hFF m h)) hra
  have hTX : ∀ j, Spike.Lib.X64.Rt.TiWAtP
      (fun s c => WSHX L a ar p Dt Cw Ctx lbl lsize (frM c0) (X0TH L (L.lab siteL)) s c ∧
        Spike.Lib.X64.HelloW2.OffW ar s)
      (Spike.Lib.X64.PhRec.K L (r1Of L.lab)) L.exe L.endPc (R.callee (-136) (-248) 8) F'
      (StackM (r1Of L.lab)) (tiQ (tH L.lab) c0 g) Spike.Lib.X64.Rt.x8L PT j := fun j =>
    Spike.Lib.X64.WakePh.TiWAtP.imp (hT j) (hL j) fun _ _ h1 h2 => ⟨h2 h1.1, h1.2⟩
  have hTn := tiWAtP_nmAt L.lays rfl hti hrc.take hTX
  -- the fields' and the take's facts under `tpXa`
  have hfld' : ∀ e ∈ Ret0.ThreadInit.fields (tH L.lab) (Ret0.stacksA L.lab + 16384#64),
      Ret0.StOk (tpXa (ms []) tp) F (tH L.lab + BitVec.ofNat 64 e.1) e.2 :=
    fun e he => stOk_tpXa (hfld e he)
  have htk' : ∀ g', Spike.Lib.X64.Rt.TakeOkA (tpXa (ms []) tp) F L.exe L.endPc
      ((R.callee (-136) (-248) 8).callee (-48 - 0) (-200) 8) F' (Ret0.tiTake (tiQ (tH L.lab) c0 g) g') :=
    fun g' => Spike.Lib.X64.WakePh.Ti2.takeOkA_tpX (htk c0 _ F' hFF rfl g g')
  have hFt : ∀ m pm, F' m → F' (Ret0.takeMem pm (r1Of L.lab) m) :=
    Ret0.takeMem_of_kstable (a := L.lab siteL) (fun s s' hk hm => hKt s s' (.inl hk) hm) L.exe L.endPc
  -- the segment, at `TakeK` of the site
  have hseg := Spike.Lib.X64.Rt.threadInit_segWAtAC (p := p) (lbl := lbl)
    (ms := tpXa (ms []) tp) (F0 := F) L.lays rfl hti hrc.take hF hR hRlo hhi hFF (tiQ (tH L.lab) c0 g)
    (by show (16384#64 : BitVec 64).toNat + 16384 ≤ 536870912; decide) hfld' htk'
    (P := Pz (r1Of L.lab)) (Spike.Lib.X64.HelloPh.Ti2.pz_fstable_ti2H hbase)
    hTn hRS hfit hout hFt
  -- off the clone's pc `TakeK` of the site is `TakeCK`
  have hseg1 := hseg.mono_K (K' := TakeCK (L.lab siteL) (r1Of L.lab) Cl)
    fun s c hw s' => by
      constructor
      · rintro (hk | ⟨hcl', -⟩)
        · exact hk
        · exact absurd (hCl s hcl') hw.1.1.2.1.1
      · exact fun hk => .inl hk
  -- `WSHX` gives `W ∧ X`
  have hseg2 := hseg1.mono_W (W' := fun s c => (W s c [] ∧ X s c []) ∧ NoSetFsAt s)
    fun s c hw => ⟨hWX c0 cA hM.1 s c hw.1.1 hw.1.2, hw.2⟩
  refine hseg2.mono_post fun s c h => ?_
  obtain ⟨x, he, hn, hdc, hpc, σ, hA, ⟨hD, hM'⟩, hJ⟩ := h
  exact ⟨x, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, hM'⟩

end Hat

end Spike.Lib.X64HelloTi2HatO

/-- info: 'Spike.Lib.X64HelloTi2HatO.hti_HOX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloTi2HatO.hti_HOX
